module

public import SHE.RandomProfileDerivative
public import SHE.SectionEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.ControlledProfile
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier ProfileL2
  ProfilePointwise ProfileStability ProfileParameter ControlledScoreRates
open scoped NNReal
local instance randomProfileEnergy_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {W : Type*} [MeasurableSpace W] [MeasurableSpace CircleL2] [BorelSpace CircleL2]

def sharpUnit (P : CanonicalCovariance.ProfileParameters) : ℝ :=
  2*meanConstant P.lower P.holder P.exponent

theorem sharpConstant_factor (P : CanonicalCovariance.ProfileParameters) (d : CircleL2) :
    sharpConstant P d=sharpUnit P*‖d‖ := by
  unfold sharpConstant sharpUnit
  ring

/-- The ACTUAL random-input profile derivative has genuine spatial and
probability energy. The random past norm is retained inside expectation;
no independence from the profile is asserted. -/
theorem random_derivative_spatial_energy (P : CanonicalCovariance.ProfileParameters)
    {Λ : ℝ} (hΛ : 0≤Λ) (u d : W→CircleL2) (hu : Measurable u) (hd : Measurable d)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (μ : Measure W) [SFinite μ] (hdi : Integrable (fun ω=>‖d ω‖^2) μ) :
    ∀ᵐ θ ∂volume,∀ᵐ r ∂volume.restrict (Ici (0:ℝ)),
      Integrable (fun z : W×HeatCircle=>|derivative P Λ (u z.1) (d z.1) ((r,z.2),θ)|^2)
        (μ.prod haarAddCircle) ∧
      (∫ z : W×HeatCircle,|derivative P Λ (u z.1) (d z.1) ((r,z.2),θ)|^2 ∂μ.prod haarAddCircle)≤
        (sharpUnit P*r^((P.exponent-1)/4))^2*(∫ ω,‖d ω‖^2 ∂μ) := by
  have hsharp := random_ae_derivative_sharp_power P hΛ u d hu hd hsmallPoint hsmallL2 μ
  have hmeas := random_derivative_measurable P hΛ u d hu hd hsmallPoint
  have hbound (θ : ℝ) : MeasurableSet {z : W×ℝ |
      normTwo haarAddCircle (fun x=>derivative P Λ (u z.1) (d z.1) ((z.2,x),θ))≤
        sharpConstant P (d z.1)*z.2^((P.exponent-1)/4)} := by
    have hm : Measurable (fun z : (W×ℝ)×HeatCircle=>derivative P Λ (u z.1.1) (d z.1.1) ((z.1.2,z.2),θ)) := by
      convert! hmeas.comp ((measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)).prodMk measurable_const) using 1
    have hn := ((hm.pow_const 2).stronglyMeasurable.integral_prod_right'
      (ν:=haarAddCircle (T:=2*π))).measurable.sqrt
    have hc : Measurable (fun z : W×ℝ=>sharpConstant P (d z.1)*z.2^((P.exponent-1)/4)) := by
      simp only [sharpConstant_factor]
      exact ((hd.norm.comp measurable_fst).const_mul _).mul (measurable_snd.pow_const _)
    exact measurableSet_le hn hc
  filter_upwards [hsharp] with θ hθ
  have he := (Measure.ae_ae_comm (hbound θ)).mp (hθ.mono (fun ω hω=>hω.mono (fun r hr=>hr.2)))
  filter_upwards [he,ae_restrict_mem measurableSet_Ici] with r hr hr0
  let F : W×HeatCircle→ℝ := fun z=>derivative P Λ (u z.1) (d z.1) ((r,z.2),θ)
  let K := sharpUnit P*r^((P.exponent-1)/4)
  have hFm : Measurable F := by
    convert! hmeas.comp ((measurable_fst.prodMk (measurable_const.prodMk measurable_snd)).prodMk measurable_const) using 1
  have hs : ∀ᵐ ω ∂μ,Integrable (fun x : HeatCircle=>‖F (ω,x)‖^2) haarAddCircle := by
    apply ae_of_all
    intro ω
    have hm : Measurable (fun x : HeatCircle=>F (ω,x)) := hFm.comp (measurable_const.prodMk measurable_id)
    have hb (x : HeatCircle) : |F (ω,x)|≤coarseConstant P (d ω)*r^((P.exponent-2)/4) :=
      derivative_coarse_power P hΛ (u ω) (d ω) hsmallPoint θ (r,x) hr0
    simpa only [Real.norm_eq_abs,sq_abs] using (bounded_memLp hm hb).integrable_sq
  have hb : ∀ᵐ ω ∂μ,(∫ x : HeatCircle,‖F (ω,x)‖^2 ∂haarAddCircle)≤K^2*‖d ω‖^2 := by
    filter_upwards [hr] with ω hω
    have hc : 0≤sharpConstant P (d ω)*r^((P.exponent-1)/4) :=
      mul_nonneg (sharpConstant_nonneg P (d ω)) (rpow_nonneg hr0 _)
    have hh := pow_le_pow_left₀ (normTwo_nonneg haarAddCircle _) hω 2
    rw [normTwo_sq] at hh
    simpa only [F,K,Real.norm_eq_abs,sq_abs,sharpConstant_factor,mul_pow,mul_assoc,mul_comm,mul_left_comm] using hh
  have hp := SectionEnergy.product_energy haarAddCircle μ F hFm (fun ω=>K^2*‖d ω‖^2)
    (hdi.const_mul _) hs hb
  refine ⟨by simpa only [F,Real.norm_eq_abs] using hp.1,?_⟩
  simpa only [F,K,Real.norm_eq_abs,integral_const_mul] using hp.2

end SHE.ControlledProfile
