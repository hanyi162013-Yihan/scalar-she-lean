module

public import SHE.HolderRandomScoreEnergy
public import SHE.InactiveFutureScoreInput
public import SHE.FractionalNormEnergy
public import SHE.RandomFutureInputFields
public import SHE.SectionEnergy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.EndpointHolderScoreEnergy
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier StoppedGaussianFeatures
  ProfileL2 ProfileStability ControlledProfile MeasurableGaussianScores ControlledResidualScoreInput
local instance : Fact (0<2*π):=⟨by positivity⟩
variable {W : Type*} [MeasurableSpace W] [MeasurableSpace CircleL2] [BorelSpace CircleL2]

/-- True newest-endpoint profile score energy, including its inactive
zero-age future coordinate. Its score mass equals the original older
frame, so only older stops require a positive gap. The actual correlated
past input energy retains its Holder power without an age loss. -/
theorem future_energy (P : CanonicalCovariance.ProfileParameters)
    {Λ : ℝ} (hΛ : 0≤Λ) (u d : W→CircleL2) (hu : Measurable u) (hd : Measurable d)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (μ : Measure W) [IsProbabilityMeasure μ] (hdi : Integrable (fun ω=>‖d ω‖^2) μ)
    (q : ℝ) (hq : 0≤q) (θ η : ℝ) (newCenter : HeatCircle)
    (n : ℕ) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ1 : ∀ i,σ i-q≤1) (hages : ∀ i,σ i≤target i)
    (hi : ℝ) (hhi : q<hi) (hstop : ∀ i,hi≤σ i)
    (ell : ℝ) (hell : 0<ell) (c : W×ControlledProfile.Domain→ℝ) (hc : Measurable c)
    (U : ℝ) (hcb : ∀ p,0≤c p ∧ c p≤U) (hcl : ∀ p,ell≤c p) :
    let e:=fun z : W×ControlledProfile.Domain=>
      profile P Λ (u z.1) (d z.1) (θ,z.2)-profile P Λ (u z.1) (d z.1) (η,z.2)
    let F:=fun z : W×HeatCircle=>futureInput (Fin.cons q σ) (Fin.cons q target) (Fin.cons newCenter center)
      (fun p=>c (z.1,p)) (fun p=>e (z.1,p)) q z.2
    let C:=2*P.holder*|θ-η|^P.exponent*(3*((n:ℝ)/ell))
    Integrable (fun z=>|F z|^2) (μ.prod haarAddCircle) ∧
      (∫ z,|F z|^2 ∂μ.prod haarAddCircle)≤C^2*(∫ ω,‖d ω‖^2 ∂μ)^P.exponent := by
  intro e F C
  have hh:=HolderRandomScoreEnergy.future_energy P hΛ u d hu hd hsmallL2 μ hdi q hq θ η n
    σ target center hσ1 hages hi hhi hstop ell hell c hc U hcb hcl
  have heq : F=(fun z : W×HeatCircle=>futureInput σ target center
      (fun p=>c (z.1,p)) (fun p=>e (z.1,p)) q z.2) := by
    funext z
    exact InactiveFutureScoreInput.future_input_eq σ target center hages q q le_rfl newCenter
      (fun p=>c (z.1,p)) (hc.comp (measurable_const.prodMk measurable_id)) hell
      (fun p=>⟨hcl (z.1,p),(hcb (z.1,p)).2⟩) (fun p=>e (z.1,p)) z.2
  rw [heq]
  exact hh

end SHE.EndpointHolderScoreEnergy
