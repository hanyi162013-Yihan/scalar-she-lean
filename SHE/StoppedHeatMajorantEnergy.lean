module
public import SHE.ParametricStoppedHaarEnergy
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
namespace SHE.StoppedHeatMajorantEnergy
open Set MeasureTheory PredictableL2 StoppedFourier
open scoped NNReal ENNReal
variable {Ω:Type*}[MeasurableSpace Ω](μ:Measure Ω)[IsProbabilityMeasure μ](H b:ℝ≥0)

/-- Exact causal square-root mass on the original full-H time measure
gives a uniform energy bound for any nonnegative dependent integrand
with the stated actual heat majorant. -/
theorem bound (hbH:b≤H)(K:ℝ)(G:ℝ≥0→Ω→ℝ≥0∞)
    (hG:∀t ω,G t ω≤ENNReal.ofReal K*(Iio b).indicator
      (fun r:ℝ≥0=>ENNReal.ofReal (((b:ℝ)-(r:ℝ))^(-(1/2:ℝ)))) t):
    (∫⁻t,∫⁻ω,G t ω ∂μ ∂timeMeasure H)≤
      ENNReal.ofReal K*ENNReal.ofReal (2*Real.sqrt H):=by
  calc
    _≤∫⁻t,ENNReal.ofReal K*(Iio b).indicator
        (fun r:ℝ≥0=>ENNReal.ofReal (((b:ℝ)-(r:ℝ))^(-(1/2:ℝ)))) t ∂timeMeasure H:=by
      apply lintegral_mono
      intro t
      calc
        _≤∫⁻_:Ω,ENNReal.ofReal K*(Iio b).indicator
            (fun r:ℝ≥0=>ENNReal.ofReal (((b:ℝ)-(r:ℝ))^(-(1/2:ℝ)))) t ∂μ:=lintegral_mono (hG t)
        _=_:=by simp
    _=ENNReal.ofReal K*ENNReal.ofReal (2*Real.sqrt b):=by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_indicator measurableSet_Iio,
        NativeStoppedBracket.timeMeasure_before hbH,causal_rpow_mass (by norm_num:(-1:ℝ) < -(1/2:ℝ))]
      norm_num only [show -(1/2:ℝ)+1=1/2 by norm_num]
      rw [Real.sqrt_eq_rpow]
      congr 2
      ring
    _≤_:=by gcongr
end SHE.StoppedHeatMajorantEnergy
