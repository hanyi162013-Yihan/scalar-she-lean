module

public import SHE.NativeVariableTerminalCap
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SHE.NativeWeightedTerminalCap
open MeasureTheory Set PredictableL2 StoppedFourier
open scoped ENNReal NNReal
variable {P Ω:Type*} [MeasurableSpace P] [MeasurableSpace Ω]

/-- The true integrable uncut history weight may multiply the moving
terminal cap before Fubini; no square of that history weight is needed. -/
theorem integrable (ν:Measure P)[IsFiniteMeasure ν](μ:Measure Ω)[IsProbabilityMeasure μ]
    (H:ℝ≥0)(T:P→ℝ)(hT:Measurable T)(hT0:∀p,0≤T p)(hTH:∀p,T p≤(H:ℝ))
    (hT1:∀p,T p≤1){M:ℝ}(hM:0≤M)
    (W:P→ℝ)(hW:Measurable W)(hW0:∀p,0≤W p)(hWi:Integrable W ν):
    Integrable (fun z:P×(ℝ≥0×Ω)=>W z.1*
      (if (z.2.1:ℝ)<T z.1 then NativeObservationCaps.cap M (T z.1-(z.2.1:ℝ)) else 0))
        (ν.prod (energyMeasure μ H)):=by
  letI:IsFiniteMeasure (energyMeasure μ H):=by dsimp only [energyMeasure];infer_instance
  let w:=fun p=>ENNReal.ofReal (W p)
  have hw:Measurable w:=hW.ennreal_ofReal
  have hfin:(∫⁻p,w p ∂ν)≠∞:=
    (lintegral_ofReal_ne_top_iff_integrable hW.aestronglyMeasurable (Filter.Eventually.of_forall hW0)).mpr hWi
  letI:IsFiniteMeasure (ν.withDensity w):=isFiniteMeasure_withDensity hfin
  have hi:=NativeVariableTerminalCap.integrable (ν.withDensity w) μ H T hT hT0 hTH hT1 hM
  rw [prod_withDensity_left hw] at hi
  have hh:=(integrable_withDensity_iff_integrable_smul' (hw.comp measurable_fst)
    (Filter.Eventually.of_forall (fun z:P×(ℝ≥0×Ω)=>ENNReal.ofReal_lt_top))).mp hi
  simpa only [w,Function.comp_def,ENNReal.toReal_ofReal (hW0 _),smul_eq_mul] using hh

end SHE.NativeWeightedTerminalCap
