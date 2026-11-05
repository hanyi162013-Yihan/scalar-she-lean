module

public import SHE.FutureInputFields
public import SHE.StoppedCovarianceInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.ControlledResidualScoreInput
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier StoppedGaussianFeatures
  ProfileL2 ProfilePointwise ProfileStability ControlledProfile ControlledScoreRates
local instance futureInputCoarse_periodPos : Fact (0<2*π) := ⟨by positivity⟩
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse

/-- A finite point bound for the literal remaining covariance input.
It is used only for spatial Fubini; the quantitative comparison keeps
the sharper spatial L2 bound. All original stopping masks are retained. -/
theorem future_input_coarse (P : CanonicalCovariance.ProfileParameters) {Λ : ℝ}
    (hΛ : 0≤Λ) (u d : CircleL2)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (θ q : ℝ) (hq : 0≤q) (old : ControlledProfile.Domain→ℝ) (hold : Measurable old)
    (holdb : ∀ p,0≤old p ∧ old p≤P.lower/2)
    (n : ℕ) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ1 : ∀ i,σ i-q≤1) (hages : ∀ i,σ i≤target i)
    (hi : ℝ) (hhi : q<hi) (hstop : ∀ i,hi≤σ i) (x : HeatCircle) :
    let c := fun p=>ControlledProfile.profile P Λ u d (θ,p)-old p
    let e := fun p=>ControlledProfile.derivative P Λ u d (p,θ)
    0≤futureInput σ target center c e q x ∧
    futureInput σ target center c e q x≤
      coarseConstant P d*((n:ℝ)/(P.lower/2))*((hi-q)/2)^((P.exponent-2)/4)*
        (1+2/(((P.exponent-2)/4)+1)) := by
  dsimp only
  rw [futureInput_eq_shifted]
  let c' : ControlledProfile.Domain→ℝ := fun p=>
    ControlledProfile.profile P Λ u d (θ,(q+p.1,p.2))-old (q+p.1,p.2)
  let e' := shiftedDerivative P Λ u d q θ
  have hc' : Measurable c' :=
    ((profile_measurable P Λ u d).comp
      (measurable_const.prodMk ((measurable_const.add measurable_fst).prodMk measurable_snd))).sub
        (hold.comp ((measurable_const.add measurable_fst).prodMk measurable_snd))
  have he' : Measurable e' := shiftedDerivative_measurable P hΛ u d hsmallPoint q θ
  have hcb (p : ControlledProfile.Domain) : 0≤c' p ∧ c' p≤P.upper := by
    have hp := profile_bounds P Λ u d (θ,(q+p.1,p.2))
    have ho := holdb (q+p.1,p.2)
    dsimp only [c']
    constructor <;> linarith [P.lower_pos]
  have hcl (p : ControlledProfile.Domain) : P.lower/2≤c' p := by
    have hp := profile_bounds P Λ u d (θ,(q+p.1,p.2))
    have ho := holdb (q+p.1,p.2)
    dsimp only [c']
    linarith
  have hs : 0<hi-q := sub_pos.mpr hhi
  have hσ (i : Fin n) : 0<σ i-q := lt_of_lt_of_le hs (sub_le_sub_right (hstop i) q)
  have hτ : -1<(P.exponent-2)/4 := by linarith [P.exponent_pos]
  have hτ0 : (P.exponent-2)/4<0 := by linarith [P.exponent_le_one]
  refine ⟨StoppedScoreLeverage.scoreInput_nonneg _ _ _ hσ hσ1
    (fun i=>sub_le_sub_right (hages i) q) c' hc' P.upper (P.lower/2) hcb
      (half_pos P.lower_pos) hcl e' x,?_⟩
  exact (StoppedCovarianceInput.score_input_weighted_bound
    (fun i=>σ i-q) (fun i=>target i-q) (fun i=>center i+x) hσ hσ1
    (fun i=>sub_le_sub_right (hages i) q) hs hτ hτ0 (coarseConstant_nonneg P d)
    (fun i=>sub_le_sub_right (hstop i) q) c' hc' P.upper (P.lower/2) hcb
    (half_pos P.lower_pos) hcl e' he'
    (fun p hp=>shiftedDerivative_coarse P hΛ u d hsmallPoint hq θ p hp)).2

end SHE.ControlledResidualScoreInput
