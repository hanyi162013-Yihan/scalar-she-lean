module

public import SHE.PastAgeFutureScoreEnergy
public import SHE.NativeFirstScoreReserve

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section
namespace SHE.ControlledResidualScoreInput
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier StoppedGaussianFeatures
  ProfileL2 ProfilePointwise ProfileStability ControlledProfile ControlledScoreRates
open scoped NNReal
local instance nativePastAgeScoreEnergy_period : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {W:Type*} [MeasurableSpace W] [MeasurableSpace CircleL2] [BorelSpace CircleL2]

/-- Actual random-past profile-input energy AFTER the independent
native reserve. The remaining floor is THREE-EIGHTHS. The ORIGINAL
past age is retained outside the score mass; there is NO fresh-gap loss. -/
theorem random_native_past_age_energy (P:CanonicalCovariance.ProfileParameters)
    {Λ:ℝ} (hΛ:0≤Λ) (u d:W→CircleL2) (hu:Measurable u) (hd:Measurable d)
    (hsmallPoint:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (μ:Measure W) [SFinite μ] (hdi:Integrable (fun ω=>‖d ω‖^2) μ):
    ∀ᵐθ∂volume,∀q:ℝ,0<q→
      ∀(old:W×ControlledProfile.Domain→ℝ),Measurable old→
      (∀p,0≤old p ∧ old p≤P.lower/2)→
      ∀(n:ℕ) (σ target:Fin n→ℝ) (center:Fin n→HeatCircle),
      (∀i,σ i-q≤1)→(∀i,σ i≤target i)→
      ∀hi:ℝ,q<hi→(∀i,hi≤σ i)→
      let c:=fun z:W×ControlledProfile.Domain=>profile P Λ (u z.1) (d z.1) (θ,z.2)-
        NativeFirstScoreReserve.oldProfile P (fun p=>old (z.1,p)) z.2
      let e:=fun z:W×ControlledProfile.Domain=>derivative P Λ (u z.1) (d z.1) (z.2,θ)
      let F:=fun z:W×HeatCircle=>futureInput σ target center
        (fun p=>c (z.1,p)) (fun p=>e (z.1,p)) q z.2
      let C:=(sharpUnit P*q^((P.exponent-1)/4))*(((n:ℝ)/(3*P.lower/8))*3)
      Integrable (fun z=>|F z|^2) (μ.prod haarAddCircle) ∧
        (∫z,|F z|^2 ∂μ.prod haarAddCircle)≤C^2*(∫ω,‖d ω‖^2 ∂μ):=by
  filter_upwards [random_past_age_future_energy P hΛ u d hu hd hsmallPoint hsmallL2 μ hdi] with θ hθ
  intro q hq old hold holdb n σ target center hσ1 hages hi hhi hstop
  have hell:0<3*P.lower/8:=by have :=P.lower_pos;positivity
  have hm:Measurable (fun z:W×ControlledProfile.Domain=>old z+NativeFirstScoreReserve.floor P):=
    hold.add_const _
  have hb(z:W×ControlledProfile.Domain):0≤old z+NativeFirstScoreReserve.floor P ∧
      old z+NativeFirstScoreReserve.floor P≤P.lower-3*P.lower/8:=by
    have hz:=holdb z
    unfold NativeFirstScoreReserve.floor
    constructor <;> linarith [P.lower_pos]
  exact hθ q hq (3*P.lower/8) hell _ hm hb n σ target center hσ1 hages hi hhi hstop

end SHE.ControlledResidualScoreInput
