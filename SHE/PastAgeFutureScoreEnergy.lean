module

public import SHE.RandomFutureInputFields
public import SHE.PastAgeFutureScoreInput
public import SHE.RandomProfileEnergy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ControlledResidualScoreInput
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier StoppedGaussianFeatures
  ProfileL2 ProfilePointwise ProfileStability ControlledProfile ControlledScoreRates
open scoped NNReal
local instance pastAgeFutureScoreEnergy_period : Fact (0<2*π) := ⟨by positivity⟩
variable {W : Type*} [MeasurableSpace W] [MeasurableSpace CircleL2] [BorelSpace CircleL2]

/-- The actual random profile mass has original past-age energy and
NO fresh-gap loss. Both covariance and signed input can depend on the
same past norm. A common theta event precedes every current age. -/
theorem random_past_age_future_energy (P : CanonicalCovariance.ProfileParameters)
    {Λ : ℝ} (hΛ : 0≤Λ) (u d : W→CircleL2) (hu : Measurable u) (hd : Measurable d)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (μ : Measure W) [SFinite μ] (hdi : Integrable (fun ω=>‖d ω‖^2) μ) :
    ∀ᵐ θ ∂volume,∀ q : ℝ,0<q →
      ∀ ell : ℝ,0<ell →
      ∀ (old : W×ControlledProfile.Domain→ℝ),Measurable old →
      (∀ p,0≤old p ∧ old p≤P.lower-ell) →
      ∀ (n : ℕ) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle),
      (∀ i,σ i-q≤1) → (∀ i,σ i≤target i) →
      ∀ hi : ℝ,q<hi → (∀ i,hi≤σ i) →
      let c := fun z : W×ControlledProfile.Domain=>profile P Λ (u z.1) (d z.1) (θ,z.2)-old z
      let e := fun z : W×ControlledProfile.Domain=>derivative P Λ (u z.1) (d z.1) (z.2,θ)
      let F := fun z : W×HeatCircle=>futureInput σ target center
        (fun p=>c (z.1,p)) (fun p=>e (z.1,p)) q z.2
      let C := (sharpUnit P*q^((P.exponent-1)/4))*(((n:ℝ)/ell)*3)
      Integrable (fun z=>|F z|^2) (μ.prod haarAddCircle) ∧
        (∫ z,|F z|^2 ∂μ.prod haarAddCircle)≤C^2*(∫ ω,‖d ω‖^2 ∂μ) := by
  filter_upwards [random_past_age_future_input P hΛ u d hu hd hsmallPoint hsmallL2 μ] with θ hθ
  intro q hq ell hell old hold holdb n σ target center hσ1 hages hi hhi hstop c e F C
  have hc : Measurable c := by
    have hmap : Measurable (fun z : W×ControlledProfile.Domain=>((z.1,θ),z.2)) :=
      (measurable_fst.prodMk measurable_const).prodMk measurable_snd
    have hh := (random_profile_measurable P hu hd Λ).comp hmap
    convert! hh.sub hold using 1
  have he : Measurable e := by
    have hmap : Measurable (fun z : W×ControlledProfile.Domain=>(z,θ)) :=
      measurable_id.prodMk measurable_const
    convert! (random_derivative_measurable P hΛ u d hu hd hsmallPoint).comp
      hmap using 1
  have hFm : Measurable F := futureInput_random_measurable σ target center c e hc he q
  have hBi : Integrable (fun ω=>C^2*‖d ω‖^2) μ := hdi.const_mul _
  have hh : ∀ᵐ ω ∂μ,Integrable (fun x : HeatCircle=>‖F (ω,x)‖^2) haarAddCircle ∧
      (∫ x : HeatCircle,‖F (ω,x)‖^2 ∂haarAddCircle)≤C^2*‖d ω‖^2 := by
    filter_upwards [hθ] with ω hω
    have ho : Measurable (fun p=>old (ω,p)) := hold.comp (measurable_const.prodMk measurable_id)
    have hp := hω q hq ell hell (fun p=>old (ω,p)) ho (fun p=>holdb (ω,p))
      n σ target center hσ1 hages hi hhi hstop
    refine ⟨hp.1.norm.integrable_sq,?_⟩
    have hpow := pow_le_pow_left₀ (normTwo_nonneg haarAddCircle _) hp.2 2
    rw [normTwo_sq] at hpow
    simpa only [F,c,e,C,sharpConstant_factor,mul_pow,mul_assoc,mul_comm,mul_left_comm,
      Real.norm_eq_abs,sq_abs] using hpow
  have hb := SectionEnergy.product_energy haarAddCircle μ F hFm
    (fun ω=>C^2*‖d ω‖^2) hBi (hh.mono (fun _ h=>h.1)) (hh.mono (fun _ h=>h.2))
  refine ⟨by simpa only [Real.norm_eq_abs] using hb.1,?_⟩
  simpa only [Real.norm_eq_abs,integral_const_mul] using hb.2

end SHE.ControlledResidualScoreInput
