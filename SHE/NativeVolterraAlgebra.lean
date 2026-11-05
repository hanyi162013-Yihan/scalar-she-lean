module
public import SHE.NativeClock
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.NativeVolterraAlgebra
open MeasureTheory Set NativeHeatObservation LowBands
open scoped NNReal

theorem integrable(Λ:ℝ)(U:ℝ≥0→StateL2)(hU:Continuous U)(t:ℝ≥0):
    IntervalIntegrable (fun s:ℝ=>Real.exp (-Λ*((t:ℝ)-s)) • heat ((t:ℝ)-s) (U s.toNNReal)) volume 0 t:=by
  have hh:=RealHeat.continuous_realHeat_action.comp
    ((show Continuous (fun s:ℝ=>((t:ℝ)-s)/timeScale) by fun_prop).prodMk
      (hU.comp continuous_real_toNNReal))
  exact ((show Continuous (fun s:ℝ=>Real.exp (-Λ*((t:ℝ)-s))) by fun_prop).smul hh).intervalIntegrable _ _

theorem sub(Λ:ℝ)(U V:ℝ≥0→StateL2)(hU:Continuous U)(hV:Continuous V)(t:ℝ≥0):
    NativeClock.volterra Λ (fun s=>U s-V s) t=NativeClock.volterra Λ U t-NativeClock.volterra Λ V t:=by
  unfold NativeClock.volterra
  calc
    _=∫s in (0:ℝ)..(t:ℝ),(Real.exp (-Λ*((t:ℝ)-s)) • heat ((t:ℝ)-s) (U s.toNNReal)-
        Real.exp (-Λ*((t:ℝ)-s)) • heat ((t:ℝ)-s) (V s.toNNReal)):=by
      apply intervalIntegral.integral_congr
      intro s _
      change Real.exp (-Λ*((t:ℝ)-s)) • heat ((t:ℝ)-s) (U s.toNNReal-V s.toNNReal)=_
      simp only [map_sub,smul_sub]
    _=_:=intervalIntegral.integral_sub (integrable Λ U hU t) (integrable Λ V hV t)
end SHE.NativeVolterraAlgebra
