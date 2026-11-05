module

public import SHE.ProfileL2
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.ConditionalSquareL1
open MeasureTheory Real ProfileL2
variable {Ω W : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure W) [SFinite ν]

/-- Conditional second-moment envelopes with an L1 spatial mass imply
GENUINE absolute product integrability. This justifies finite linearity
and Fubini before taking a signed spatial average. -/
theorem joint_integrable (F : Ω×W→ℝ) (hF : Measurable F)
    (H : W→ℝ) (hHi : Integrable H ν) (hH : ∀ w,0≤H w)
    {C : ℝ} (hC : 0≤C)
    (hi : ∀ᵐ w ∂ν,Integrable (fun ω=>|F (ω,w)|^2) μ)
    (hb : ∀ᵐ w ∂ν,(∫ ω,|F (ω,w)|^2 ∂μ)≤C*(H w)^2) :
    Integrable F (μ.prod ν) ∧
      (∫ z,|F z| ∂μ.prod ν)≤sqrt C*(∫ w,H w ∂ν) := by
  have hmem : ∀ᵐ w ∂ν,MemLp (fun ω=>F (ω,w)) 2 μ := by
    filter_upwards [hi] with w hw
    apply (memLp_two_iff_integrable_sq (hF.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr
    simpa only [sq_abs,Function.comp_apply,id_eq] using hw
  have hnorm : ∀ᵐ w ∂ν,(∫ ω,‖F (ω,w)‖ ∂μ)≤sqrt C*H w := by
    filter_upwards [hmem,hb] with w hw hwb
    have hone : MemLp (fun _ : Ω=>(1:ℝ)) 2 μ:=memLp_const 1
    have hc:=integral_mul_normTwo_bound hone hw.norm
    have he : normTwo μ (fun _ : Ω=>(1:ℝ))=1:=by
      simp only [normTwo,one_pow,integral_const,probReal_univ,smul_eq_mul,mul_one,sqrt_one]
    have hn : normTwo μ (fun ω=>‖F (ω,w)‖)≤sqrt C*H w := by
      unfold normTwo
      have hh:=sqrt_le_sqrt hwb
      rw [sqrt_mul hC,sqrt_sq_eq_abs,abs_of_nonneg (hH w)] at hh
      simpa only [Real.norm_eq_abs,sq_abs] using hh
    have hc' : (∫ ω,‖F (ω,w)‖ ∂μ)≤normTwo μ (fun ω=>‖F (ω,w)‖):=by
      exact (le_abs_self _).trans (by simpa only [he,one_mul] using hc)
    exact hc'.trans hn
  have hj : Integrable F (μ.prod ν):=by
    apply (integrable_prod_iff' hF.aestronglyMeasurable).mpr
    refine ⟨hmem.mono (fun _ hw=>hw.integrable (by norm_num)),?_⟩
    apply (hHi.const_mul (sqrt C)).mono'
      hF.norm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
    filter_upwards [hnorm] with w hw
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _=>norm_nonneg _))]
    exact hw
  refine ⟨hj,?_⟩
  change (∫ z,‖F z‖ ∂μ.prod ν)≤_
  rw [integral_prod_symm _ hj.norm]
  have hh:=integral_mono_ae hj.norm.integral_prod_right (hHi.const_mul (sqrt C)) hnorm
  simpa only [Real.norm_eq_abs,integral_const_mul] using hh

end SHE.ConditionalSquareL1
