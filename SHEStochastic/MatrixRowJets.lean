module

public import SHEStochastic.MatrixRowEntries
public import SHEStochastic.MatrixNegativeJets

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHEStochastic.MatrixRowJets
open MeasureTheory SHE SHE.FiniteHaar SHE.DyadicApproximation SHE.HaarWeightedHeat SHE.CellNegative
open MatrixInfiniteHaar MatrixPhysicalColumnSmooth MatrixActualColumnCalculus MatrixProfileEntries MatrixNegativeEntries
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable {d : Type*} [Fintype d] [DecidableEq d]

def orderConstant (P : Profile d) (k : ℕ) : ℝ :=
  MatrixTransformedJets.profileConstant P (MatrixRowEntries.boundedConstant d * MatrixDirectionBounds.profileBound P) k *
    MatrixRowEntries.boundedConstant d ^ k
def packetConstant (P : Profile d) (ρ : ℝ) (k : ℕ) : ℝ := 2 * MatrixRowEntries.slotConstant ρ * orderConstant P k

theorem orderConstant_nonneg (P : Profile d) (k : ℕ) : 0 ≤ orderConstant P k := by
  have hD : 0 ≤ MatrixRowEntries.boundedConstant d := zero_le_one.trans MatrixRowEntries.bounded_one_le
  have hP : 0 ≤ MatrixDirectionBounds.profileBound P := by
    have hU := P.upper_pos
    unfold MatrixDirectionBounds.profileBound
    positivity
  exact mul_nonneg (MatrixTransformedJets.profileConstant_nonneg P _ (mul_nonneg hD hP) k) (pow_nonneg hD k)

theorem packetConstant_nonneg (P : Profile d) (ρ : ℝ) (k : ℕ) : 0 ≤ packetConstant P ρ k :=
  mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans (MatrixRowEntries.slot_one_le ρ))) (orderConstant_nonneg P k)

theorem branch {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (P : Profile d) (p : List Bool) (L : ℝ) (hL : 0 < L) (u : C(AddCircle (1 : ℝ),ℂ))
    (hu : ∀ b : Bool, ∀ y ∈ cellSet (p.length+1) (bottomLeaf p b), ‖u y‖ ≤ 2*L/(((2^(p.length+1):ℕ):ℝ)))
    (hlip : ∀ b : Bool, ∀ y ∈ cellSet (p.length+1) (bottomLeaf p b),
      ∀ z ∈ cellSet (p.length+1) (bottomLeaf p b), ‖u y-u z‖ ≤ L*dist y z)
    (b : Bool) (v : Domain (d := d)) (w : List (Domain (d := d)))
    (B : Domain (d := d) → ℝ) (hB : ∀ q, 0 ≤ B q) (hRest : ∀ q ∈ w, ∀ᵐ x ∂μ, ‖q.val x‖ ≤ B q) :
    MatrixTransformedJets.expression P p b (MatrixRowEntries.operator p L u) (v :: w) ≤
      (Real.sqrt (childLength p))⁻¹ * MatrixRowEntries.slotConstant ρ * orderConstant P w.length *
        scale Λ ρ (p.length+1) * localNorm p Λ ρ hΛ hρ.le v * MatrixJetClosure.weight B w := by
  let D := MatrixRowEntries.boundedConstant d
  let β := MatrixRowEntries.slotConstant ρ * scale Λ ρ (p.length+1) * localNorm p Λ ρ hΛ hρ.le v
  have hD1 : 1 ≤ D := MatrixRowEntries.bounded_one_le
  have hD : 0 ≤ D := zero_le_one.trans hD1
  have hP : 0 ≤ MatrixDirectionBounds.profileBound P := by
    have hU := P.upper_pos
    unfold MatrixDirectionBounds.profileBound
    positivity
  have hβ : 0 ≤ β := mul_nonneg (mul_nonneg (zero_le_one.trans (MatrixRowEntries.slot_one_le ρ))
    (scale_positive Λ ρ hΛ _).le) (localNorm_nonneg p Λ ρ hΛ hρ.le v)
  have hm : MatrixActualCoefficientBounds.weight p v ≤ (Real.sqrt (childLength p))⁻¹ * β := by
    apply (mass_weight hΛ hρ hρhalf p v).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hh := mul_le_mul_of_nonneg_right (le_max_left (negativeSlotConstant ρ) (rowSlotConstant ρ))
      (mul_nonneg (scale_positive Λ ρ hΛ (p.length+1)).le (localNorm_nonneg p Λ ρ hΛ hρ.le v))
    simpa only [β, MatrixRowEntries.slotConstant, mul_assoc] using hh
  have hh := MatrixTransformedJets.one_input P p b (MatrixRowEntries.operator p L u) v w (fun q => D*B q)
    (fun q => mul_nonneg hD (hB q)) (D*MatrixDirectionBounds.profileBound P) β (mul_nonneg hD hP) hβ
    (MatrixRowEntries.local_bounded p L hL u hu b (MatrixProfileSymmetry.realize d P)
      (MatrixDirectionBounds.profileBound P) hP (MatrixDirectionBounds.profile_bound P))
    (MatrixRowEntries.distinguished hΛ hρ hρhalf p L hL u hu hlip b v) hm (by
      intro q hq
      constructor
      · apply (MatrixDirectionBounds.weight_bounded p q (B q) (hB q) (hRest q hq)).trans
        have hh := mul_le_mul_of_nonneg_right hD1 (hB q)
        nlinarith only [hh]
      · exact MatrixRowEntries.local_bounded p L hL u hu b q (B q) (hB q) (hRest q hq))
  rw [MatrixNegativeJets.weight_scale] at hh
  exact hh.trans_eq (by unfold orderConstant; dsimp only [D, β]; ring)

/-- Actual higher matrix Haar jets against a centered spatial row.
Only the explicit scalar amplitude/Lipschitz hypotheses are used. -/
theorem packet {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (P : Profile d) (p : List Bool) (L : ℝ) (hL : 0 < L) (u : C(AddCircle (1 : ℝ),ℂ))
    (hu : ∀ b : Bool, ∀ y ∈ cellSet (p.length+1) (bottomLeaf p b), ‖u y‖ ≤ 2*L/(((2^(p.length+1):ℕ):ℝ)))
    (hlip : ∀ b : Bool, ∀ y ∈ cellSet (p.length+1) (bottomLeaf p b),
      ∀ z ∈ cellSet (p.length+1) (bottomLeaf p b), ‖u y-u z‖ ≤ L*dist y z)
    (i r : d) (v : Domain (d := d)) (w : List (Domain (d := d)))
    (B : Domain (d := d) → ℝ) (hB : ∀ q, 0 ≤ B q) (hRest : ∀ q ∈ w, ∀ᵐ x ∂μ, ‖q.val x‖ ≤ B q) :
    ‖CellRow.row u (realEmbed (component r (MatrixPhysicalJetStructure.jetColumn P p i (v :: w))))‖ ≤
      packetConstant P ρ w.length * (L/(((2^(p.length+1):ℕ):ℝ))) * scale Λ ρ (p.length+1) *
        localNorm p Λ ρ hΛ hρ.le v * MatrixJetClosure.weight B w := by
  have hh := (MatrixTransformedJets.bound P p i r (MatrixRowEntries.operator p L u) (v :: w)).trans
    (add_le_add (branch hΛ hρ hρhalf P p L hL u hu hlip false v w B hB hRest)
      (branch hΛ hρ hρhalf P p L hL u hu hlip true v w B hB hRest))
  change ‖rowScale (p.length+1) L • CellRow.row u
    (realEmbed (component r (MatrixPhysicalJetStructure.jetColumn P p i (v :: w))))‖ ≤ _ at hh
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (rowScale_positive _ hL)] at hh
  apply (mul_le_mul_iff_right₀ (rowScale_positive (p.length+1) hL)).mp
  apply hh.trans_eq
  rw [sqrt_child_inverse]
  have he := rowScale_mul (p.length+1) hL
  calc
    _ = packetConstant P ρ w.length * (rowScale (p.length+1) L * (L/(((2^(p.length+1):ℕ):ℝ)))) *
      scale Λ ρ (p.length+1) * localNorm p Λ ρ hΛ hρ.le v * MatrixJetClosure.weight B w := by
      rw [he]
      unfold packetConstant
      ring
    _ = _ := by ring

end SHEStochastic.MatrixRowJets
