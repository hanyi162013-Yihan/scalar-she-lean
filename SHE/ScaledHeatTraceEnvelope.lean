module
public import SHE.HaarKernelL2Approximation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.ScaledHeatTraceEnvelope
open MeasureTheory Set Filter PredictableL2 CompanionHeat
open scoped Topology NNReal ENNReal
variable {Ω:Type*}[MeasurableSpace Ω]

def constant(M scale:ℝ):ℝ:=
  M*(1+2*HeatTrace.fractionalGaussianIntegral 0*scale^((1/2:ℝ)))

theorem constant_nonneg{M scale:ℝ}(hM:0≤M)(hs:0≤scale):0≤constant M scale:=by
  have hC:0≤HeatTrace.fractionalGaussianIntegral 0:=
    (HeatTrace.fractionalGaussianIntegral_pos (by norm_num:(0:ℝ)<1/2)).le
  unfold constant
  positivity

/-- Physical time rescaling changes only the fixed heat-trace constant. -/
theorem scalar_bound{M scale u:ℝ}(hM:0≤M)(hs:0<scale)(hu:0<u)(hu1:u≤1):
    M*(1+2*HeatTrace.fractionalGaussianIntegral 0*(u/scale)^(-(1/2:ℝ)))≤
      constant M scale*u^(-(1/2:ℝ)):=by
  have hC:0≤HeatTrace.fractionalGaussianIntegral 0:=
    (HeatTrace.fractionalGaussianIntegral_pos (by norm_num:(0:ℝ)<1/2)).le
  have hp:1≤u^(-(1/2:ℝ)):=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu hu1 (by norm_num)
  have he:(u/scale)^(-(1/2:ℝ))=u^(-(1/2:ℝ))*scale^((1/2:ℝ)):=by
    rw [Real.div_rpow hu.le hs.le,Real.rpow_neg hs.le,div_inv_eq_mul]
  rw [he]
  unfold constant
  nlinarith [mul_le_mul_of_nonneg_left hp hM]

def envelope(h:ℝ≥0)(M scale:ℝ)(p:ℝ≥0×(ℝ≥0×Ω)):ℝ≥0∞:=
  ENNReal.ofReal (constant M scale)*picardKernel h ((p.1:ℝ)-(p.2.1:ℝ))

theorem measurable(h:ℝ≥0)(M scale:ℝ):Measurable (envelope (Ω:=Ω) h M scale):=
  measurable_const.mul ((picardKernel_measurable h).comp
    ((measurable_coe_nnreal_real.comp measurable_fst).sub
      (measurable_coe_nnreal_real.comp measurable_snd.fst)))

/-- The causal square-root kernel remains integrable on the full
outer/inner time square; its zero extension removes the upper triangle. -/
theorem square_finite(μ:Measure Ω)[IsProbabilityMeasure μ](h:ℝ≥0)(M scale:ℝ):
    (∫⁻p,envelope h M scale p ∂HaarKernelL2Approximation.measure μ h)<∞:=by
  let C:=ENNReal.ofReal (constant M scale)
  have hm:=measurable (Ω:=Ω) h M scale
  have hs(t:ℝ≥0)(ht:t≤h):
      (∫⁻s,picardKernel h ((t:ℝ)-(s:ℝ)) ∂timeMeasure h)=
        ∫⁻s,picardKernel h ((t:ℝ)-(s:ℝ)) ∂timeMeasure t:=by
    rw [←timeMeasure_restrict ht,←lintegral_indicator measurableSet_Ioc]
    apply lintegral_congr_ae
    filter_upwards [timeMeasure_ae_mem h] with s hs
    by_cases hst:s≤t
    · rw [Set.indicator_of_mem (show s∈Ioc 0 t from ⟨hs.1,hst⟩)]
    · rw [Set.indicator_of_notMem (show s∉Ioc 0 t from fun hh=>hst hh.2)]
      have hneg:(t:ℝ)-(s:ℝ)≤0:=sub_nonpos.mpr (by exact_mod_cast (le_of_not_ge hst))
      unfold picardKernel
      exact Set.indicator_of_notMem (fun hh=>not_lt_of_ge hneg hh.1) _
  have he:(∫⁻p,envelope h M scale p ∂HaarKernelL2Approximation.measure μ h)=
      C*(∫⁻t,∫⁻s,picardKernel h ((t:ℝ)-(s:ℝ))*1 ∂timeMeasure t ∂timeMeasure h):=by
    unfold HaarKernelL2Approximation.measure
    rw [lintegral_prod _ hm.aemeasurable]
    have hi:(∫⁻t,∫⁻p,envelope h M scale (t,p) ∂(timeMeasure h).prod μ ∂timeMeasure h)=
        ∫⁻t,C*(∫⁻s,picardKernel h ((t:ℝ)-(s:ℝ)) ∂timeMeasure t) ∂timeMeasure h:=by
      apply lintegral_congr_ae
      filter_upwards [timeMeasure_ae_mem h] with t ht
      have hmt:Measurable (fun p:ℝ≥0×Ω=>envelope h M scale (t,p)):=
        hm.comp (measurable_const.prodMk measurable_id)
      rw [lintegral_prod _ hmt.aemeasurable]
      simp only [envelope,lintegral_const,measure_univ,mul_one]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,hs t ht.2]
    rw [hi,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    simp only [mul_one]
    rfl
  rw [he]
  apply lt_of_le_of_lt (mul_le_mul_right
    (predictable_picard_causal_energy h (fun _=>1) measurable_const) C)
  rw [timeMeasure_one_integral]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
end SHE.ScaledHeatTraceEnvelope
