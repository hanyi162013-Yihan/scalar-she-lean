module

public import SHE.WeightedSpatialMoments
public import SHE.ProfileL2

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.SpatialMarkAveraging
open Set Filter MeasureTheory ProbabilityTheory Real ProfileL2
variable {Ω X W : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace W]
variable (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure X) [SFinite ν]

/-- A variable spatial L2 envelope supplies genuine product
integrability before probability and output integration are exchanged. -/
theorem variable_fiber_second_moment (F : Ω×X→ℝ) (hF : Measurable F)
    (G : X→ℝ) (hG : MemLp G 2 ν) {C : ℝ} (hC : 0≤C)
    (hi : ∀ᵐ x ∂ν,Integrable (fun ω=>|F (ω,x)|^2) μ)
    (hb : ∀ᵐ x ∂ν,(∫ ω,|F (ω,x)|^2 ∂μ)≤C*(G x)^2) :
    Integrable (fun z=>|F z|^2) (μ.prod ν) ∧
      (∫ z,|F z|^2 ∂μ.prod ν)≤C*(normTwo ν G)^2 := by
  have hm : Measurable (fun z=>|F z|^2) := (continuous_abs.measurable.comp hF).pow_const _
  have hj : Integrable (fun z=>|F z|^2) (μ.prod ν) := by
    apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
    refine ⟨hi,?_⟩
    apply (hG.integrable_sq.const_mul C).mono'
      hm.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
    filter_upwards [hb] with x hx
    simp only [Real.norm_eq_abs,abs_pow,abs_abs]
    rw [abs_of_nonneg (integral_nonneg (fun _=>sq_nonneg _))]
    exact hx
  refine ⟨hj,?_⟩
  rw [integral_prod_symm _ hj,normTwo_sq,←integral_const_mul]
  exact integral_mono_ae hj.integral_prod_right (hG.integrable_sq.const_mul C) hb

/-- Old-space averaging precedes the output L2 norm. The final envelope
is the spatial L1 average, not its square average or a supremum. This
retains the sharp one-input forest gain for dependent Gaussian marks. -/
theorem averaged_second_moment (η : Measure W) [IsProbabilityMeasure η]
    (F : (Ω×X)×W→ℝ) (hF : Measurable F) (H : X×W→ℝ) (hHm : Measurable H)
    (hH : ∀ x w,0≤H (x,w)) (hHi : ∀ x,Integrable (fun w=>H (x,w)) η)
    (hG : MemLp (fun x=>∫ w,H (x,w) ∂η) 2 ν) {C : ℝ} (hC : 0≤C)
    (hi : ∀ᵐ x ∂ν,∀ᵐ w ∂η,Integrable (fun ω=>|F ((ω,x),w)|^2) μ)
    (hb : ∀ᵐ x ∂ν,∀ᵐ w ∂η,(∫ ω,|F ((ω,x),w)|^2 ∂μ)≤C*(H (x,w))^2) :
    Integrable (fun z : Ω×X=>|∫ w,F (z,w) ∂η|^2) (μ.prod ν) ∧
      (∫ z : Ω×X,|∫ w,F (z,w) ∂η|^2 ∂μ.prod ν)≤
        C*(normTwo ν (fun x=>∫ w,H (x,w) ∂η))^2 := by
  have hA : Measurable (fun z : Ω×X=>∫ w,F (z,w) ∂η) :=
    hF.stronglyMeasurable.integral_prod_right'.measurable
  have havg : ∀ᵐ x ∂ν,Integrable (fun ω=>|∫ w,F ((ω,x),w) ∂η|^2) μ ∧
      (∫ ω,|∫ w,F ((ω,x),w) ∂η|^2 ∂μ)≤C*(∫ w,H (x,w) ∂η)^2 := by
    filter_upwards [hi,hb] with x hx hb
    have hpair : Measurable (fun z : Ω×W=>((z.1,x),z.2)) :=
      (measurable_fst.prodMk measurable_const).prodMk measurable_snd
    have hF' : Measurable (fun z : Ω×W=>F ((z.1,x),z.2)) := by
      convert! hF.comp hpair using 1
    have hpairH : Measurable (fun w : W=>(x,w)) := measurable_const.prodMk measurable_id
    have hH' : Measurable (fun w=>H (x,w)) := by convert! hHm.comp hpairH using 1
    simpa only [mul_one] using WeightedSpatialMoments.nonnegative_envelope μ η
      (fun z : Ω×W=>F ((z.1,x),z.2)) hF' (fun w=>H (x,w)) hH' (hHi x) (hH x)
      1 zero_lt_one C hC hx hb
  exact variable_fiber_second_moment μ ν _ hA _ hG hC
    (havg.mono (fun _ h=>h.1)) (havg.mono (fun _ h=>h.2))

end SHE.SpatialMarkAveraging
