module

public import SHEStochastic.MatrixNegativeEntries
public import SHE.HaarRowPacket

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.MatrixRowEntries
open MeasureTheory SHE SHE.FiniteHaar SHE.DyadicApproximation SHE.HaarWeightedHeat SHE.CellNegative
open MatrixInfiniteHaar MatrixPhysicalColumnSmooth MatrixActualColumnCalculus MatrixProfileEntries MatrixNegativeEntries
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable {d : Type*} [Fintype d] [DecidableEq d]

def operator (p : List Bool) (L : ℝ) (u : C(AddCircle (1 : ℝ),ℂ)) : RealL2 →L[ℝ] ℂ :=
  (scaledRow (p.length+1) L u).comp realEmbed
def boundedConstant (d : Type*) [Fintype d] : ℝ := 1 + 2 * (Fintype.card d : ℝ) ^ 2
def slotConstant (ρ : ℝ) : ℝ := max (negativeSlotConstant ρ) (rowSlotConstant ρ)

theorem slot_one_le (ρ : ℝ) : 1 ≤ slotConstant ρ := (le_max_right _ _).trans (le_max_left _ _)
theorem bounded_one_le : 1 ≤ boundedConstant d := by unfold boundedConstant; nlinarith [sq_nonneg (Fintype.card d : ℝ)]

theorem restricted (p : List Bool) (b : Bool) (L : ℝ) (u : C(AddCircle (1 : ℝ),ℂ))
    (v : Domain (d := d)) (r j : d) :
    operator p L u (entry r j (MatrixPhysicalColumnSmooth.restricted (MatrixGlobalHaar.child p b)
      (MatrixGlobalHaar.child_measurable p b) v)) =
    rowScale (p.length+1) L • CellRow.row u
      (cellRestriction (p.length+1) (bottomLeaf p b) (realEmbed (entry r j v.val))) := by
  change rowScale (p.length+1) L • CellRow.row u (realEmbed (entry r j
    (MatrixPhysicalColumnMap.restriction (cellSet (p.length+1) (bottomLeaf p b)) (measurableSet_cellSet _ _) v.val))) = _
  rw [MatrixCellEntries.restricted_entry]

theorem local_bounded (p : List Bool) (L : ℝ) (hL : 0 < L) (u : C(AddCircle (1 : ℝ),ℂ))
    (hu : ∀ b : Bool, ∀ y ∈ cellSet (p.length+1) (bottomLeaf p b),
      ‖u y‖ ≤ 2*L/(((2^(p.length+1):ℕ):ℝ)))
    (b : Bool) (v : Domain (d := d)) (B : ℝ) (hB : 0 ≤ B) (hv : ∀ᵐ x ∂μ, ‖v.val x‖ ≤ B) :
    MatrixTransformedJets.localSize p b (operator p L u) v ≤
      (boundedConstant d * B) * Real.sqrt (childLength p) := by
  let N : ℝ := ((2^(p.length+1):ℕ):ℝ)
  have hN : 0 < N := by dsimp [N]; positivity
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have ht (r j : d) : ‖operator p L u (entry r j (MatrixPhysicalColumnSmooth.restricted
      (MatrixGlobalHaar.child p b) (MatrixGlobalHaar.child_measurable p b) v))‖ ≤ 2*B*Real.sqrt (childLength p) := by
    rw [restricted, norm_smul, Real.norm_eq_abs, abs_of_pos (rowScale_positive _ hL)]
    have hh := CellRow.row_bounded (bottomLeaf p b) u L hL.le (hu b) (realEmbed (entry r j v.val)) B hB
      (entry_bounded v.val B hv r j)
    apply (mul_le_mul_of_nonneg_left hh (rowScale_positive _ hL).le).trans_eq
    have hfour : (Real.sqrt N)^4 = N^2 := by nlinarith [congrArg (fun x : ℝ => x^2) (Real.sq_sqrt hN.le)]
    rw [childLength, Real.sqrt_inv]
    change (Real.sqrt N)^3/L*(2*L*B/N^2) = 2*B*(Real.sqrt N)⁻¹
    rw [← hfour]
    field_simp [hL.ne', hs.ne']
  calc
    _ ≤ ∑ r : d, ∑ j : d, 2*B*Real.sqrt (childLength p) :=
      Finset.sum_le_sum (fun r _ => Finset.sum_le_sum (fun j _ => ht r j))
    _ = 2*(Fintype.card d : ℝ)^2*B*Real.sqrt (childLength p) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ _ := by
      unfold boundedConstant
      nlinarith [mul_nonneg hB (Real.sqrt_nonneg (childLength p))]

theorem distinguished {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (p : List Bool) (L : ℝ) (hL : 0 < L) (u : C(AddCircle (1 : ℝ),ℂ))
    (hu : ∀ b : Bool, ∀ y ∈ cellSet (p.length+1) (bottomLeaf p b), ‖u y‖ ≤ 2*L/(((2^(p.length+1):ℕ):ℝ)))
    (hlip : ∀ b : Bool, ∀ y ∈ cellSet (p.length+1) (bottomLeaf p b),
      ∀ z ∈ cellSet (p.length+1) (bottomLeaf p b), ‖u y-u z‖ ≤ L*dist y z)
    (b : Bool) (v : Domain (d := d)) :
    MatrixTransformedJets.localSize p b (operator p L u) v ≤
      slotConstant ρ * scale Λ ρ (p.length+1) * localNorm p Λ ρ hΛ hρ.le v := by
  have hs : 0 < Real.sqrt (((2^(p.length+1):ℕ):ℝ)) := by positivity
  have ht (r j : d) : ‖operator p L u (entry r j (MatrixPhysicalColumnSmooth.restricted
      (MatrixGlobalHaar.child p b) (MatrixGlobalHaar.child_measurable p b) v))‖ ≤
      Real.sqrt (SmoothCellSobolev.packetConstant ρ)*scale Λ ρ (p.length+1)*
        ‖MatrixNegativeEntries.operator Λ ρ hΛ hρ.le (entry r j
          (MatrixPhysicalColumnSmooth.restricted (MatrixGlobalHaar.child p b) (MatrixGlobalHaar.child_measurable p b) v))‖ := by
    rw [restricted, norm_smul, Real.norm_eq_abs, abs_of_pos (rowScale_positive _ hL)]
    have hh := CellRow.row_negative hΛ hρ hρhalf (p.length+1) (bottomLeaf p b) u L hL.le
      (hu b) (hlip b) (realEmbed (entry r j v.val))
    change _ ≤ Real.sqrt (SmoothCellSobolev.packetConstant ρ)*scale Λ ρ (p.length+1)*
      ‖besselHalf Λ ρ hΛ hρ.le (realEmbed (entry r j
        (MatrixPhysicalColumnMap.restriction (cellSet (p.length+1) (bottomLeaf p b)) (measurableSet_cellSet _ _) v.val)))‖
    rw [MatrixCellEntries.restricted_entry]
    apply (mul_le_mul_of_nonneg_left hh (rowScale_positive (p.length+1) hL).le).trans_eq
    unfold rowScale
    field_simp [hL.ne', hs.ne']
  have hcoef : Real.sqrt (SmoothCellSobolev.packetConstant ρ) ≤ slotConstant ρ :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hlocal : MatrixTransformedJets.localSize p b (MatrixNegativeEntries.operator Λ ρ hΛ hρ.le) v ≤
      localNorm p Λ ρ hΛ hρ.le v := by
    cases b
    · exact le_add_of_nonneg_right (transformedSize_nonneg _ _)
    · exact le_add_of_nonneg_left (transformedSize_nonneg _ _)
  calc
    _ ≤ Real.sqrt (SmoothCellSobolev.packetConstant ρ)*scale Λ ρ (p.length+1)*
        MatrixTransformedJets.localSize p b (MatrixNegativeEntries.operator Λ ρ hΛ hρ.le) v := by
      simp only [MatrixTransformedJets.localSize, transformedSize, Finset.mul_sum]
      exact Finset.sum_le_sum (fun r _ => Finset.sum_le_sum (fun j _ => ht r j))
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right hcoef (scale_positive Λ ρ hΛ _).le)
      hlocal (transformedSize_nonneg _ _) (mul_nonneg (zero_le_one.trans (slot_one_le ρ)) (scale_positive Λ ρ hΛ _).le)

end SHEStochastic.MatrixRowEntries
