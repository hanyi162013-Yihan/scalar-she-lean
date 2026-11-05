module

public import SHEStochastic.MatrixRootNegativeSlots

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.MatrixRootNegative
open MeasureTheory SHE SHE.FiniteHaar SHE.DyadicApproximation SHE.CircleHeat SHE.HaarWeightedHeat
open MatrixInfiniteHaar MatrixPhysicalColumnSmooth MatrixProfileEntries MatrixRootNegativeSlots
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable {d : Type*} [Fintype d] [DecidableEq d]

def orderConstant (P : Profile d) (k : ℕ) : ℝ :=
  MatrixRootTransforms.profileConstant P (count d * MatrixDirectionBounds.profileBound P) k * count d ^ k

theorem orderConstant_nonneg (P : Profile d) (k : ℕ) : 0 ≤ orderConstant P k := by
  have hp : 0 ≤ MatrixDirectionBounds.profileBound P := by
    have hU := P.upper_pos
    unfold MatrixDirectionBounds.profileBound
    positivity
  exact mul_nonneg (MatrixRootTransforms.profileConstant_nonneg P _ (mul_nonneg (zero_le_one.trans count_one) hp) k)
    (pow_nonneg (zero_le_one.trans count_one) _)

def scalarColumn (P : Profile d) (i r : d) (w : List (Domain (d := d))) : CircleL2 :=
  realEmbed (component r (DirectionalJets.jet w (MatrixRootCalculus.root i) (MatrixProfileSymmetry.realize d P)))

theorem transformed_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : CircleL2 →L[ℝ] E) (hT : ∀ z, ‖T z‖ ≤ ‖z‖) (P : Profile d) (i r : d)
    (v : Domain (d := d)) (w : List (Domain (d := d))) (M : Domain (d := d) → ℝ)
    (hM : ∀ q, 0 ≤ M q) (hRest : ∀ q ∈ w, ∀ᵐ x ∂μ, ‖q.val x‖ ≤ M q)
    (β : ℝ) (hβ : 0 ≤ β) (hv : transformedSize (T.comp realEmbed) v.val ≤ β)
    (hm : MatrixRootCalculus.perturbation v ≤ β) :
    ‖T (scalarColumn P i r (v :: w))‖ ≤
      orderConstant P w.length * β *
        MatrixJetClosure.weight M w := by
  have hD : 0 ≤ count d := zero_le_one.trans count_one
  have hP : 0 ≤ MatrixDirectionBounds.profileBound P := by
    have hU := P.upper_pos
    unfold MatrixDirectionBounds.profileBound
    positivity
  have hh := MatrixRootTransforms.one_input P i r (T.comp realEmbed) v w
    (fun q => count d * M q) (fun q => mul_nonneg hD (hM q))
    (count d * MatrixDirectionBounds.profileBound P)
    β
    (mul_nonneg hD hP) hβ
    (transformed_bounded T hT _ _ hP (MatrixDirectionBounds.profile_bound P))
    hv hm (by
      intro q hq
      constructor
      · have hqB := (MatrixRootJets.perturbation_norm q).trans (MatrixRootJets.norm_bounded q (M q) (hM q) (hRest q hq))
        have hm := mul_le_mul_of_nonneg_right (count_one (d := d)) (hM q)
        nlinarith [hM q]
      · exact transformed_bounded T hT q (M q) (hM q) (hRest q hq))
  rw [MatrixNegativeJets.weight_scale] at hh
  exact hh.trans_eq (by dsimp only [orderConstant]; ring)

theorem normalized_bound {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (ht : 0 < t) (ht1 : t ≤ 1) (b : CircleL2) (B : ℝ) (hB : 0 < B)
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ B) (P : Profile d) (i r : d)
    (v : Domain (d := d)) (w : List (Domain (d := d))) (M : Domain (d := d) → ℝ)
    (hM : ∀ q, 0 ≤ M q) (hRest : ∀ q ∈ w, ∀ᵐ x ∂μ, ‖q.val x‖ ≤ M q) :
    ‖normalizedConstantOutput Λ ρ t hΛ hρ.le b B hb (scalarColumn P i r (v :: w))‖ ≤
      orderConstant P w.length * NegativeConstantOutput.scale Λ ρ t * negativeSize Λ ρ hΛ hρ.le v *
        MatrixJetClosure.weight M w := by
  exact (transformed_bound (normalizedConstantOutput Λ ρ t hΛ hρ.le b B hb)
    (normalizedConstantOutput_contraction hΛ hρ.le b B hB hb) P i r v w M hM hRest
    (NegativeConstantOutput.scale Λ ρ t * negativeSize Λ ρ hΛ hρ.le v)
    (mul_nonneg (NegativeConstantOutput.scale_nonneg _ _ _) (negativeSize_nonneg _ _ _ _ _))
    (output hΛ hρ hρhalf ht ht1 b B hB hb v) (mass hΛ hρ.le ht ht1 v)).trans_eq (by ring)

/-- The actual root columns obey the same negative distinguished
input estimate as the infinite details, after an arbitrary bounded
scalar output multiplier. No time- or mass-dependent constants occur. -/
theorem pointwise {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (ht : 0 < t) (ht1 : t ≤ 1) (b : CircleL2) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ B) (P : Profile d) (i r : d)
    (v : Domain (d := d)) (w : List (Domain (d := d))) (M : Domain (d := d) → ℝ)
    (hM : ∀ q, 0 ≤ M q) (hRest : ∀ q ∈ w, ∀ᵐ x ∂μ, ‖q.val x‖ ≤ M q) :
    ‖weightedHeat Λ ρ t hΛ hρ.le b B hb (scalarColumn P i r (v :: w))‖^2 ≤
      (2 * orderConstant P w.length^2 * count d) * B^2 * t^(-(1/2 : ℝ)) *
        MatrixNegativeLocalization.energy Λ ρ v * MatrixJetClosure.weight M w^2 := by
  by_cases hB0 : B = 0
  · have hz := weightedHeat_norm_le Λ ρ t hΛ hρ.le b B hB hb (scalarColumn P i r (v :: w))
    simp only [hB0, zero_mul] at hz
    have he := le_antisymm hz (norm_nonneg _)
    simp only [he, hB0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_mul, le_refl]
  have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
  have hh := pow_le_pow_left₀ (norm_nonneg _)
    (normalized_bound hΛ hρ hρhalf ht ht1 b B hBp hb P i r v w M hM hRest) 2
  rw [normalizedConstantOutput_sq, mul_pow, mul_pow, mul_pow, NegativeConstantOutput.scale_sq hΛ ht] at hh
  have hq := mul_le_mul_of_nonneg_left hh (sq_nonneg B)
  have hcancel : B^2 * (Λ^ρ / B^2 * ‖weightedHeat Λ ρ t hΛ hρ.le b B hb (scalarColumn P i r (v :: w))‖^2) =
      Λ^ρ * ‖weightedHeat Λ ρ t hΛ hρ.le b B hb (scalarColumn P i r (v :: w))‖^2 := by field_simp
  rw [hcancel] at hq
  have hraw : ‖weightedHeat Λ ρ t hΛ hρ.le b B hb (scalarColumn P i r (v :: w))‖^2 ≤
      2 * orderConstant P w.length^2 * B^2 * t^(-(1/2 : ℝ)) *
        negativeSize Λ ρ hΛ hρ.le v^2 * MatrixJetClosure.weight M w^2 := by
    apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos (zero_lt_one.trans_le hΛ) ρ)).mp
    exact hq.trans_eq (by ring)
  have hm := mul_le_mul_of_nonneg_left (negativeSize_sq hΛ hρ.le v)
    (by positivity : 0 ≤ 2 * orderConstant P w.length^2 * B^2 * t^(-(1/2 : ℝ)) * MatrixJetClosure.weight M w^2)
  exact hraw.trans (by nlinarith only [hm])

end SHEStochastic.MatrixRootNegative
