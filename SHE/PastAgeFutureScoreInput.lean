module

public import SHE.PastAgeResidualScoreInput
public import SHE.FutureInputCoarse

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ControlledResidualScoreInput
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier StoppedGaussianFeatures
  ProfileL2 ProfilePointwise ProfileStability ControlledProfile ControlledScoreRates
open scoped NNReal
local instance pastAgeFutureScoreInput_period : Fact (0<2*π) := ⟨by positivity⟩
variable {W : Type*} [MeasurableSpace W] [MeasurableSpace CircleL2] [BorelSpace CircleL2]

/-- The literal future input has its ORIGINAL positive past-age rate,
with no remaining-gap loss. Distinct stops and true targets are retained
under the actual time translation. -/
theorem random_past_age_future_input (P : CanonicalCovariance.ProfileParameters)
    {Λ : ℝ} (hΛ : 0≤Λ) (u d : W→CircleL2) (hu : Measurable u) (hd : Measurable d)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (μ : Measure W) [SFinite μ] :
    ∀ᵐ θ ∂volume,∀ᵐ ω ∂μ,∀ q : ℝ,0<q →
      ∀ ell : ℝ,0<ell →
      ∀ (old : ControlledProfile.Domain→ℝ),Measurable old →
      (∀ p,0≤old p ∧ old p≤P.lower-ell) →
      ∀ (n : ℕ) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle),
      (∀ i,σ i-q≤1) → (∀ i,σ i≤target i) →
      ∀ hi : ℝ,q<hi → (∀ i,hi≤σ i) →
      let c := fun p=>ControlledProfile.profile P Λ (u ω) (d ω) (θ,p)-old p
      let e := fun p=>ControlledProfile.derivative P Λ (u ω) (d ω) (p,θ)
      let F := futureInput σ target center c e q
      MemLp F 2 haarAddCircle ∧ normTwo haarAddCircle F≤
        (sharpConstant P (d ω)*q^((P.exponent-1)/4))*(((n:ℝ)/ell)*3) := by
  filter_upwards [random_past_age_shifted_input P hΛ u d hu hd hsmallPoint hsmallL2 μ] with θ hθ
  filter_upwards [hθ] with ω hω
  intro q hq ell hell old hold holdb n σ target center hσ1 hages hi hhi hstop c e F
  have hs : 0<hi-q := sub_pos.mpr hhi
  have hσ (i : Fin n) : 0<σ i-q := lt_of_lt_of_le hs (sub_le_sub_right (hstop i) q)
  have hages' (i : Fin n) : σ i-q≤target i-q := sub_le_sub_right (hages i) q
  have holdm : Measurable (fun p : ControlledProfile.Domain=>old (q+p.1,p.2)) :=
    hold.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hh := hω q hq ell hell (fun p=>old (q+p.1,p.2)) holdm
    (fun p=>holdb (q+p.1,p.2)) n (fun i=>σ i-q) (fun i=>target i-q) center
    hσ hσ1 hages' (hi-q) hs (fun i=>sub_le_sub_right (hstop i) q)
  have heq : F=StoppedScoreLeverage.scoreInput (fun i=>σ i-q) (fun i=>target i-q) center
      (fun p=>ControlledProfile.profile P Λ (u ω) (d ω) (θ,(q+p.1,p.2))-old (q+p.1,p.2))
      (shiftedDerivative P Λ (u ω) (d ω) q θ) := by
    exact futureInput_eq_shifted P Λ (u ω) (d ω) q θ old σ target center
  simpa only [←heq] using hh


end SHE.ControlledResidualScoreInput
