module

public import SHEStochastic.MatrixNegativeEntries

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.MatrixNegativeBounded
open MeasureTheory SHE SHE.FiniteHaar SHE.DyadicApproximation SHE.HaarWeightedHeat SHE.CellNegative
open MatrixInfiniteHaar MatrixPhysicalColumnSmooth MatrixActualColumnCalculus MatrixProfileEntries MatrixNegativeEntries
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable {d : Type*} [Fintype d] [DecidableEq d]

def constant (d : Type*) [Fintype d] (ρ : ℝ) : ℝ := 1 + (Fintype.card d : ℝ) ^ 2 * cellConstant ρ
theorem one_le (ρ : ℝ) : 1 ≤ constant d ρ := by
  have hh : 0 ≤ (Fintype.card d : ℝ) ^ 2 * cellConstant ρ := by unfold cellConstant; positivity
  unfold constant
  linarith
theorem nonneg (ρ : ℝ) : 0 ≤ constant d ρ := zero_le_one.trans (one_le ρ)

/-- Bounded matrix directions in every transformed numerator slot
are controlled by the existing scalar localized Bessel estimate. -/
theorem local_bounded {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (p : List Bool) (b : Bool) (v : Domain (d := d)) (B : ℝ) (hB : 0 ≤ B)
    (hv : ∀ᵐ x ∂μ, ‖v.val x‖ ≤ B) :
    MatrixTransformedJets.localSize p b (scaled Λ ρ hΛ hρ.le (p.length+1)) v ≤
      (constant d ρ * B) * Real.sqrt (childLength p) := by
  have hc : 0 ≤ cellConstant ρ := by unfold cellConstant; positivity
  have ht (r j : d) :
      ‖scaled Λ ρ hΛ hρ.le (p.length+1)
        (entry r j (restricted (MatrixGlobalHaar.child p b) (MatrixGlobalHaar.child_measurable p b) v))‖ ≤
      cellConstant ρ * B * Real.sqrt (childLength p) := by
    change ‖scale Λ ρ (p.length+1) • besselHalf Λ ρ hΛ hρ.le
      (realEmbed (entry r j (restricted (MatrixGlobalHaar.child p b) (MatrixGlobalHaar.child_measurable p b) v)))‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (scale_positive Λ ρ hΛ _)]
    have he := MatrixCellEntries.restricted_entry (p.length+1) (bottomLeaf p b) v.val r j
    change realEmbed (entry r j (restricted (MatrixGlobalHaar.child p b) (MatrixGlobalHaar.child_measurable p b) v)) = _ at he
    rw [he]
    have hh := scaled_bessel_cell_le hΛ hρ hρhalf (p.length+1) (bottomLeaf p b) (realEmbed (entry r j v.val))
    have hb := cellRestriction_bounded_norm (p.length+1) (bottomLeaf p b) (realEmbed (entry r j v.val)) B hB
      (entry_bounded v.val B hv r j)
    exact hh.trans ((mul_le_mul_of_nonneg_left hb hc).trans_eq (by
      rw [childLength, Real.sqrt_inv]
      ring))
  calc
    _ ≤ ∑ r : d, ∑ j : d, cellConstant ρ * B * Real.sqrt (childLength p) :=
      Finset.sum_le_sum (fun r _ => Finset.sum_le_sum (fun j _ => ht r j))
    _ = (Fintype.card d : ℝ) ^ 2 * cellConstant ρ * B * Real.sqrt (childLength p) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ _ := by
      have hb : 0 ≤ B * Real.sqrt (childLength p) := mul_nonneg hB (Real.sqrt_nonneg _)
      unfold constant
      nlinarith only [hb]

theorem distinguished {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ)
    (p : List Bool) (b : Bool) (v : Domain (d := d)) :
    MatrixTransformedJets.localSize p b (scaled Λ ρ hΛ hρ.le (p.length+1)) v ≤
      negativeSlotConstant ρ * scale Λ ρ (p.length+1) * localNorm p Λ ρ hΛ hρ.le v := by
  have hb : MatrixTransformedJets.localSize p b (operator Λ ρ hΛ hρ.le) v ≤ localNorm p Λ ρ hΛ hρ.le v := by
    cases b
    · exact le_add_of_nonneg_right (transformedSize_nonneg _ _)
    · exact le_add_of_nonneg_left (transformedSize_nonneg _ _)
  have he : MatrixTransformedJets.localSize p b (scaled Λ ρ hΛ hρ.le (p.length+1)) v =
      scale Λ ρ (p.length+1) * MatrixTransformedJets.localSize p b (operator Λ ρ hΛ hρ.le) v := size_scaled _ _ _ _ _ _
  rw [he]
  have hc : 1 ≤ negativeSlotConstant ρ := le_max_right _ _
  calc
    _ ≤ scale Λ ρ (p.length+1) * localNorm p Λ ρ hΛ hρ.le v :=
      mul_le_mul_of_nonneg_left hb (scale_positive Λ ρ hΛ (p.length+1)).le
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right hc (mul_nonneg (scale_positive Λ ρ hΛ (p.length+1)).le
        (localNorm_nonneg p Λ ρ hΛ hρ.le v))
      simpa only [one_mul, mul_assoc] using hh

end SHEStochastic.MatrixNegativeBounded
