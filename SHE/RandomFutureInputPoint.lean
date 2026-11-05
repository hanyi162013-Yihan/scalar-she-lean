module

public import SHE.RandomFutureInputEnergy
public import SHE.FutureInputIntegrable

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ControlledResidualScoreInput
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier StoppedGaussianFeatures
  ProfileL2 ProfilePointwise ProfileStability ControlledProfile ControlledScoreRates
local instance : Fact (0<2*π) := ⟨by positivity⟩
variable {W : Type*} [MeasurableSpace W] [MeasurableSpace CircleL2] [BorelSpace CircleL2]

/-- Coarse bounds prove the true random mass square is integrable at
EVERY fixed output point and parameter. This is an applicability result;
the quantitative covariance estimate uses the sharper product energy. -/
theorem random_future_point_integrable (P : CanonicalCovariance.ProfileParameters)
    {Λ : ℝ} (hΛ : 0≤Λ) (u d : W→CircleL2) (hu : Measurable u) (hd : Measurable d)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (μ : Measure W) [SFinite μ] (hdi : Integrable (fun ω=>‖d ω‖^2) μ)
    (θ q : ℝ) (hq : 0≤q) (old : W×ControlledProfile.Domain→ℝ) (hold : Measurable old)
    (holdb : ∀ p,0≤old p ∧ old p≤P.lower/2)
    (n : ℕ) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ1 : ∀ i,σ i-q≤1) (hages : ∀ i,σ i≤target i)
    (hi : ℝ) (hhi : q<hi) (hstop : ∀ i,hi≤σ i) (x : HeatCircle) :
    let c := fun z : W×ControlledProfile.Domain=>profile P Λ (u z.1) (d z.1) (θ,z.2)-old z
    let e := fun z : W×ControlledProfile.Domain=>derivative P Λ (u z.1) (d z.1) (z.2,θ)
    Integrable (fun ω=>(futureInput σ target center (fun p=>c (ω,p)) (fun p=>e (ω,p)) q x)^2) μ := by
  intro c e
  let G : W→ℝ := fun ω=>futureInput σ target center (fun p=>c (ω,p)) (fun p=>e (ω,p)) q x
  let K : ℝ := 2*(meanConstant P.lower P.holder P.exponent*sqrt (1+heatConstant))*
    ((n:ℝ)/(P.lower/2))*((hi-q)/2)^((P.exponent-2)/4)*(1+2/(((P.exponent-2)/4)+1))
  have hc : Measurable c := by
    have hmap : Measurable (fun z : W×ControlledProfile.Domain=>((z.1,θ),z.2)) :=
      (measurable_fst.prodMk measurable_const).prodMk measurable_snd
    convert! ((random_profile_measurable P hu hd Λ).comp hmap).sub hold using 1
  have he : Measurable e := by
    have hmap : Measurable (fun z : W×ControlledProfile.Domain=>(z,θ)) :=
      measurable_id.prodMk measurable_const
    convert! (random_derivative_measurable P hΛ u d hu hd hsmallPoint).comp hmap using 1
  have hm : Measurable G := by
    convert! (futureInput_random_measurable σ target center c e hc he q).comp
      (measurable_id.prodMk (measurable_const (a:=x))) using 1
  have hb (ω : W) : |G ω|^2≤K^2*‖d ω‖^2 := by
    have ho : Measurable (fun p=>old (ω,p)) := hold.comp (measurable_const.prodMk measurable_id)
    have hh := future_input_coarse P hΛ (u ω) (d ω) hsmallPoint θ q hq
      (fun p=>old (ω,p)) ho (fun p=>holdb (ω,p)) n σ target center hσ1 hages hi hhi hstop x
    have hdom : |G ω|≤K*‖d ω‖ := by
      rw [abs_of_nonneg hh.1]
      convert! hh.2 using 1
      dsimp only [K,coarseConstant]
      ring
    simpa only [mul_pow] using pow_le_pow_left₀ (abs_nonneg _) hdom 2
  apply (hdi.const_mul (K^2)).mono' (hm.pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω=>by simpa only [Real.norm_eq_abs,abs_pow,sq_abs] using hb ω)

end SHE.ControlledResidualScoreInput
