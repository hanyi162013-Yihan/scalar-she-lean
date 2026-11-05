module
public import SHE.NativeHeatQuadratic
public import SHE.PositiveKernelMarginal
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.NativeGaussianSpatialSchur
open Set MeasureTheory Real AddCircle StoppedFourier NativeHeatQuadratic
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩

/-- The actual native positive heat kernel preserves BOTH displacement
amplitudes while producing its clipped spatial Gaussian mass. -/
theorem bound {t M A0:ℝ}(ht:0<t)(hM:0≤M)(hA0:0≤A0)
    (G:HeatCircle×HeatCircle→ℝ)(hG:Measurable G)
    (hG0:∀z,0≤G z)(hG1:∀z,G z≤1)
    (hr:∀x,(∫y:HeatCircle,G (x,y) ∂haarAddCircle)≤M)
    (hc:∀y,(∫x:HeatCircle,G (x,y) ∂haarAddCircle)≤M)
    (A:HeatCircle→ℝ)(hA:Measurable A)(hAb:∀x,|A x|≤A0):
    (∫x:HeatCircle,∫y:HeatCircle,K t ht (x,y)*G (x,y)*A x*A y ∂haarAddCircle ∂haarAddCircle)≤
      min 1 ((1+heatConstant*(t/2)^(-(1/2:ℝ)))*M)*(∫x:HeatCircle,A x^2 ∂haarAddCircle):=by
  let C:ℝ:=1+heatConstant*(t/2)^(-(1/2:ℝ))
  have hC:0≤C:=by
    dsimp [C]
    exact add_nonneg (by norm_num)
      (mul_nonneg heatConstant_pos.le (Real.rpow_nonneg (by positivity) _))
  let Q:HeatCircle×HeatCircle→ℝ:=fun z=>K t ht z*G z
  have hQ:Measurable Q:=(measurable_K ht).mul hG
  have hQ0(z:HeatCircle×HeatCircle):0≤Q z:=mul_nonneg (norm_nonneg _) (hG0 z)
  have hQb(z:HeatCircle×HeatCircle):Q z≤C:=
    (mul_le_of_le_one_right (norm_nonneg _) (hG1 z)).trans (K_bound ht z)
  have hrow(x:HeatCircle):(∫y:HeatCircle,Q (x,y) ∂haarAddCircle)≤min 1 (C*M):=by
    exact PositiveKernelMarginal.clipped haarAddCircle (fun y=>K t ht (x,y)) (fun y=>G (x,y))
      ((measurable_K ht).comp (measurable_const.prodMk measurable_id))
      (hG.comp (measurable_const.prodMk measurable_id)) hC (fun y=>norm_nonneg _)
      (fun y=>K_bound ht (x,y)) (K_row ht x) (fun y=>hG0 (x,y))
      (fun y=>hG1 (x,y)) (hr x)
  have hcol(y:HeatCircle):(∫x:HeatCircle,Q (x,y) ∂haarAddCircle)≤min 1 (C*M):=by
    exact PositiveKernelMarginal.clipped haarAddCircle (fun x=>K t ht (x,y)) (fun x=>G (x,y))
      ((measurable_K ht).comp (measurable_id.prodMk measurable_const))
      (hG.comp (measurable_id.prodMk measurable_const)) hC (fun x=>norm_nonneg _)
      (fun x=>K_bound ht (x,y)) (K_col ht y) (fun x=>hG0 (x,y))
      (fun x=>hG1 (x,y)) (hc y)
  exact PositiveKernelSchur.bounded haarAddCircle Q hQ hC
    (le_min (by norm_num) (mul_nonneg hC hM)) hA0 hQ0 hQb hrow hcol A hA hAb

end SHE.NativeGaussianSpatialSchur
