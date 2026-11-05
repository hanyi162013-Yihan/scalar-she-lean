module

public import SHE.ControlledScoreRates
public import SHE.StoppedScoreL2
public import SHE.StoppedCovarianceWordFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
noncomputable section

namespace SHE.ControlledResidualScoreInput
open Set MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier StoppedGaussianFeatures
  ProfileL2 ProfilePointwise ProfileStability ControlledProfile ControlledScoreRates
open scoped NNReal
local instance controlledResidualScoreInput_periodPos : Fact (0 < 2 * π) := ⟨by positivity⟩

/-- The signed actual controlled-profile derivative acts as one spatial
L2 input on every full positive residual. One common parameter event
works for all observation lists and all fixed old fractions below half
the floor; no pointwise spatial bound is used for the sharp rate. -/
theorem actual_residual_one_input (P : CanonicalCovariance.ProfileParameters) {Λ : ℝ}
    (hΛ : 0 ≤ Λ) (u d : CircleL2)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4) ≤ 1/2)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4) ≤ 1/2) :
    ∀ᵐ θ ∂volume,∀ (old : ControlledProfile.Domain → ℝ),Measurable old →
      (∀ p,0 ≤ old p ∧ old p ≤ P.lower/2) →
      ∀ (n : ℕ) (σ target : Fin n → ℝ) (center : Fin n → HeatCircle),
      (∀ i,0 < σ i) → (∀ i,σ i ≤ 1) → (∀ i,σ i ≤ target i) →
      ∀ (s : ℝ),0 < s → (∀ i,s ≤ σ i) →
      let c := fun p => ControlledProfile.profile P Λ u d (θ,p)-old p
      let e := fun p => ControlledProfile.derivative P Λ u d (p,θ)
      let F := StoppedScoreLeverage.scoreInput σ target center c e
      MemLp F 2 haarAddCircle ∧ normTwo haarAddCircle F ≤
        sharpConstant P d*(((n:ℝ)/(P.lower/2))*(s/2)^((P.exponent-1)/4)*
          (1+2/(((P.exponent-1)/4)+1))) := by
  filter_upwards [ae_derivative_sharp_power P hΛ u d hsmallPoint hsmallL2] with θ hsharp
  intro old hold holdb n σ target center hσ hσ1 hages s hs hstop c e F
  have hc : Measurable c :=
    ((profile_measurable P Λ u d).comp (measurable_const.prodMk measurable_id)).sub hold
  have he : Measurable e :=
    (derivative_measurable P hΛ u d hsmallPoint).comp (measurable_id.prodMk measurable_const)
  have hcb (p : ControlledProfile.Domain) : 0 ≤ c p ∧ c p ≤ P.upper := by
    have hp := profile_bounds P Λ u d (θ,p)
    have ho := holdb p
    dsimp only [c]
    constructor <;> linarith [P.lower_pos]
  have hcl (p : ControlledProfile.Domain) : P.lower/2 ≤ c p := by
    have hp := profile_bounds P Λ u d (θ,p)
    have ho := holdb p
    dsimp only [c]
    linarith
  have hcoarse (p : ControlledProfile.Domain) (hp : 0 ≤ p.1) :
      |e p| ≤ coarseConstant P d*p.1^((P.exponent-2)/4) :=
    derivative_coarse_power P hΛ u d hsmallPoint θ p hp
  have hα : -1 < (P.exponent-1)/4 := by linarith [P.exponent_pos]
  have hα0 : (P.exponent-1)/4 ≤ 0 := by linarith [P.exponent_le_one]
  have hτ : -1 < (P.exponent-2)/4 := by linarith [P.exponent_pos]
  have hτ0 : (P.exponent-2)/4 < 0 := by linarith [P.exponent_le_one]
  have hFm : Measurable F := by
    convert! StoppedCovarianceWordFields.scoreInput_measurable σ target center c e hc he using 1
  have hF0 (x : HeatCircle) : 0 ≤ F x :=
    StoppedScoreLeverage.scoreInput_nonneg σ target center hσ hσ1 hages c hc P.upper (P.lower/2)
      hcb (half_pos P.lower_pos) hcl e x
  have hFb (x : HeatCircle) : F x ≤
      coarseConstant P d*((n:ℝ)/(P.lower/2))*(s/2)^((P.exponent-2)/4)*
        (1+2/(((P.exponent-2)/4)+1)) :=
    (StoppedCovarianceInput.score_input_weighted_bound σ target (fun i => center i+x)
      hσ hσ1 hages hs hτ hτ0 (coarseConstant_nonneg P d) hstop c hc P.upper (P.lower/2)
      hcb (half_pos P.lower_pos) hcl e he hcoarse).2
  refine ⟨bounded_memLp hFm (fun x => by rw [abs_of_nonneg (hF0 x)];exact hFb x),?_⟩
  exact StoppedScoreLeverage.scoreInput_normTwo_bound σ target center hσ hσ1 hages hs hα hα0 hτ hτ0
    (half_pos P.lower_pos) (sharpConstant_nonneg P d) (coarseConstant_nonneg P d) hstop
    c hc P.upper hcb hcl e he hcoarse hsharp hFm

end SHE.ControlledResidualScoreInput
