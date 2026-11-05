module

public import SHE.NativeClock
public import SHE.PredictableTime

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.NativeObservedVolterra
open MeasureTheory Set PredictableL2 NativeHeatObservation LowBands StoppedFourier
open scoped NNReal ENNReal

/-- A positive-gap heat observation of the constructed control forcing
is the scalar Volterra integral of the original-target observations. -/
theorem observe (Λ : ℝ) {U : ℝ≥0→StateL2} (hU : Continuous U)
    (t : ℝ≥0) {T : ℝ} (hT : (t:ℝ)<T) (x : HeatCircle) :
    functional (T-(t:ℝ)) x (NativeClock.volterra Λ U t)=
      ∫ s,Real.exp (-Λ*((t:ℝ)-(s:ℝ))) • functional (T-(s:ℝ)) x (U s) ∂timeMeasure t := by
  let V : ℝ→StateL2 := fun s => Real.exp (-Λ*((t:ℝ)-s)) •
    heat ((t:ℝ)-s) (U s.toNNReal)
  have hc : Continuous V := by
    have hh := RealHeat.continuous_realHeat_action.comp
      ((show Continuous (fun s : ℝ => ((t:ℝ)-s)/timeScale) by fun_prop).prodMk
        (hU.comp continuous_real_toNNReal))
    have he : Continuous (fun s : ℝ => Real.exp (-Λ*((t:ℝ)-s))) := by fun_prop
    exact he.smul hh
  have hi : IntervalIntegrable V volume (0:ℝ) (t:ℝ) := hc.intervalIntegrable _ _
  change functional (T-(t:ℝ)) x (∫ s in (0:ℝ)..(t:ℝ),V s)=_
  rw [← (functional (T-(t:ℝ)) x).intervalIntegral_comp_comm hi]
  rw [timeMeasure_integral,intervalIntegral.integral_of_le (show 0≤(t:ℝ) from t.2)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  change functional (T-(t:ℝ)) x (V s)=
    Real.exp (-Λ*((t:ℝ)-(s.toNNReal:ℝ))) • functional (T-(s.toNNReal:ℝ)) x (U s.toNNReal)
  rw [Real.coe_toNNReal _ hs.1.le]
  dsimp only [V]
  rw [map_smul,functional_heat (sub_pos.mpr hT) (sub_nonneg.mpr hs.2)]
  rw [show T-(t:ℝ)+((t:ℝ)-s)=T-s by ring]

end SHE.NativeObservedVolterra
