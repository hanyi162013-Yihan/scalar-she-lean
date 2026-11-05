module

public import SHEStochastic.MatrixNegativeBounded

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHEStochastic.MatrixNegativeJets
open MeasureTheory SHE SHE.FiniteHaar SHE.DyadicApproximation SHE.HaarWeightedHeat SHE.CellNegative
open MatrixInfiniteHaar MatrixPhysicalColumnSmooth MatrixActualColumnCalculus MatrixProfileEntries MatrixNegativeEntries
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem weight_scale (D : ℝ) (B : Domain (d := d) → ℝ) (w : List (Domain (d := d))) :
    MatrixJetClosure.weight (fun q => D * B q) w = D ^ w.length * MatrixJetClosure.weight B w := by
  induction w with
  | nil => simp [MatrixJetClosure.weight]
  | cons v w ih =>
    simp only [MatrixJetClosure.weight, List.map_cons, List.prod_cons, List.length_cons] at *
    rw [ih, pow_succ]
    ring

def orderConstant (P : Profile d) (ρ : ℝ) (k : ℕ) : ℝ :=
  (2 : ℝ)^k * (MatrixNegativeBounded.constant d ρ * MatrixDirectionBounds.profileBound P *
      MatrixActualCoefficientBounds.constant d P.lower P.upper (k+1) +
    ((k : ℝ)+1) * MatrixActualCoefficientBounds.constant d P.lower P.upper k) *
    MatrixNegativeBounded.constant d ρ ^ k

theorem branch {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (P : Profile d) (p : List Bool) (b : Bool) (v : Domain (d := d))
    (w : List (Domain (d := d))) (B : Domain (d := d) → ℝ) (hB : ∀ q, 0 ≤ B q)
    (hRest : ∀ q ∈ w, ∀ᵐ x ∂μ, ‖q.val x‖ ≤ B q) :
    MatrixTransformedJets.expression P p b (scaled Λ ρ hΛ hρ.le (p.length+1)) (v :: w) ≤
      scale Λ ρ (p.length+1) * ((Real.sqrt (childLength p))⁻¹ * negativeSlotConstant ρ *
        orderConstant P ρ w.length * localNorm p Λ ρ hΛ hρ.le v * MatrixJetClosure.weight B w) := by
  let D := MatrixNegativeBounded.constant d ρ
  let C := MatrixActualCoefficientBounds.constant d P.lower P.upper
  let R : Domain (d := d) → ℝ := MatrixTransformedJets.localSize p b (scaled Λ ρ hΛ hρ.le (p.length+1))
  let β := negativeSlotConstant ρ * scale Λ ρ (p.length+1) * localNorm p Λ ρ hΛ hρ.le v
  have hD : 0 ≤ D := MatrixNegativeBounded.nonneg (d := d) ρ
  have hD1 : 1 ≤ D := MatrixNegativeBounded.one_le (d := d) ρ
  have hP : 0 ≤ MatrixDirectionBounds.profileBound P := by
    have hU := P.upper_pos
    unfold MatrixDirectionBounds.profileBound
    positivity
  have hβ : 0 ≤ β := mul_nonneg (mul_nonneg (zero_le_one.trans (le_max_right _ _))
    (scale_positive Λ ρ hΛ _).le) (localNorm_nonneg p Λ ρ hΛ hρ.le v)
  have ha := MatrixNegativeBounded.local_bounded hΛ hρ hρhalf p b
    (MatrixProfileSymmetry.realize d P) (MatrixDirectionBounds.profileBound P) hP (MatrixDirectionBounds.profile_bound P)
  have hh := AffineOneInputBound.one_input C (MatrixActualCoefficientBounds.constant_nonnegative P)
    (MatrixActualCoefficientBounds.weight p) R (fun q => D * B q)
    (MatrixActualCoefficientBounds.weight_nonnegative p) (fun q => mul_nonneg hD (hB q))
    (Real.sqrt (childLength p)) (Real.sqrt_pos.mpr (childLength_pos p))
    (R (MatrixProfileSymmetry.realize d P)) (D * MatrixDirectionBounds.profileBound P) β
    (mul_nonneg hD hP) hβ ha v (MatrixNegativeBounded.distinguished hΛ hρ p b v)
    (mass_weight hΛ hρ hρhalf p v) w (by
      intro q hq
      constructor
      · apply (MatrixDirectionBounds.weight_bounded p q (B q) (hB q) (hRest q hq)).trans
        have hdq := mul_le_mul_of_nonneg_right hD1 (hB q)
        nlinarith only [hdq]
      · exact MatrixNegativeBounded.local_bounded hΛ hρ hρhalf p b q (B q) (hB q) (hRest q hq))
  rw [weight_scale] at hh
  apply hh.trans_eq
  unfold orderConstant
  dsimp only [D, β]
  ring

/-- Actual all-order matrix Haar derivatives satisfy the negative
one-input estimate in every vector output component. The scalar
inverse/localization results are reused on signed covariance entries;
no multiplication of a distribution by a rough profile is assumed. -/
theorem one_input {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (P : Profile d) (p : List Bool) (i r : d) (v : Domain (d := d))
    (w : List (Domain (d := d))) (B : Domain (d := d) → ℝ) (hB : ∀ q, 0 ≤ B q)
    (hRest : ∀ q ∈ w, ∀ᵐ x ∂μ, ‖q.val x‖ ≤ B q) :
    ‖operator Λ ρ hΛ hρ.le (component r (MatrixPhysicalJetStructure.jetColumn P p i (v :: w)))‖ ≤
      2 * (Real.sqrt (childLength p))⁻¹ * negativeSlotConstant ρ * orderConstant P ρ w.length *
        localNorm p Λ ρ hΛ hρ.le v * MatrixJetClosure.weight B w := by
  have hh := (MatrixTransformedJets.bound P p i r (scaled Λ ρ hΛ hρ.le (p.length+1)) (v :: w)).trans
    (add_le_add (branch hΛ hρ hρhalf P p false v w B hB hRest) (branch hΛ hρ hρhalf P p true v w B hB hRest))
  change ‖scale Λ ρ (p.length+1) • operator Λ ρ hΛ hρ.le
    (component r (MatrixPhysicalJetStructure.jetColumn P p i (v :: w)))‖ ≤ _ at hh
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (scale_positive Λ ρ hΛ _)] at hh
  apply (mul_le_mul_iff_right₀ (scale_positive Λ ρ hΛ (p.length+1))).mp
  exact hh.trans_eq (by ring)

end SHEStochastic.MatrixNegativeJets
