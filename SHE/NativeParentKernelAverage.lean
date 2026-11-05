module
public import SHE.NativeKernelParameterAverage
public import SHE.ParentHeatFields
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.NativeParentKernelAverage
open Set MeasureTheory StoppedFourier OrderedHeatForests AddCircle
open scoped ENNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {Ω:Type*}[MeasurableSpace Ω]

/-- The ORIGINAL parent-forest spatial mass is integrated once BEFORE
squaring the actual negative-output kernel average. -/
theorem energy (μ:Measure Ω)[IsProbabilityMeasure μ]
    {m k:ℕ}(t:Fin (m+k)→ℝ)(ht:OrderedTimes k t)(a:Fin m→HeatCircle)
    (F:((Fin k→HeatCircle)×Ω)×(HeatCircle×HeatCircle)→ℂ)(hF:Measurable F)
    (B:ℝ)(hB:0≤B)(hb:∀p y x,‖F (p,(y,x))‖≤B)
    {mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)
    (C:ℝ)(hC:0≤C)
    (hi:∀ᵐw:Fin k→HeatCircle∂Measure.pi (fun _=>haarAddCircle),
      Integrable (fun ω=>‖NativeRandomKernel.negativeKernel mass ρ hmass hρ F (w,ω)‖^2) μ)
    (he:∀ᵐw:Fin k→HeatCircle∂Measure.pi (fun _=>haarAddCircle),
      (∫ω,‖NativeRandomKernel.negativeKernel mass ρ hmass hρ F (w,ω)‖^2 ∂μ)≤
        C*(parentDensity 2 (by norm_num) k t ht (values a k w))^2):
    Integrable (fun ω=>‖NativeRandomKernel.negativeKernel mass ρ hmass hρ
      (NativeKernelParameterAverage.spatialAverage (Measure.pi (fun _:Fin k=>haarAddCircle)) F) ω‖^2) μ ∧
      (∫ω,‖NativeRandomKernel.negativeKernel mass ρ hmass hρ
        (NativeKernelParameterAverage.spatialAverage (Measure.pi (fun _:Fin k=>haarAddCircle)) F) ω‖^2 ∂μ)≤
          C*(Fintype.card (Choices m k):ℝ)^2:=by
  let ν:Measure (Fin k→HeatCircle):=Measure.pi (fun _=>haarAddCircle)
  let P: (Fin k→HeatCircle)→ℝ:=fun w=>parentDensity 2 (by norm_num) k t ht (values a k w)
  have hPc:Continuous P:=(parentDensity_continuous 2 (by norm_num) k t ht).comp (values_continuous a k)
  have hPi:Integrable P ν:=hPc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hP0:∀w,0≤P w:=fun w=>parentDensity_nonneg 2 (by norm_num) k t ht _
  have hh:=NativeKernelParameterAverage.energy ν μ hF hB hb hmass hρ
    (fun w=>Real.sqrt C*P w) (hPc.measurable.const_mul _) (hPi.const_mul _)
    (fun w=>mul_nonneg (Real.sqrt_nonneg _) (hP0 w)) hi
    (he.mono (fun w hw=>by simpa only [mul_pow,Real.sq_sqrt hC] using hw))
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  rw [integral_const_mul]
  have hm:(∫w,P w ∂ν)=(Fintype.card (Choices m k):ℝ):=parentDensity_mass 2 (by norm_num) k t ht a
  rw [hm,mul_pow,Real.sq_sqrt hC]
end SHE.NativeParentKernelAverage
