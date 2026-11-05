module
public import SHE.PredictableTime
public import SHE.TimeMeasureMass
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.NativeRealOutputClock
open MeasureTheory Set PredictableL2
open scoped NNReal
variable {Ω E:Type*}[MeasurableSpace Ω][NormedAddCommGroup E]
  [MeasurableSpace E][BorelSpace E][SecondCountableTopology E]

/-- Exact original real/native output-clock transport, before any
solution-field specialization. -/
theorem energy(μ:Measure Ω)[SFinite μ](H:ℝ≥0)(Y:ℝ×Ω→E)(hY:Measurable Y)
    (hi:Integrable (fun z=>‖Y z‖^2) ((volume.restrict (Ioc (0:ℝ) (H:ℝ))).prod μ)):
    Integrable (fun z:ℝ≥0×Ω=>‖Y ((z.1:ℝ),z.2)‖^2) (energyMeasure μ H) ∧
      (∫z:ℝ≥0×Ω,‖Y ((z.1:ℝ),z.2)‖^2 ∂energyMeasure μ H)=
        (∫z:ℝ×Ω,‖Y z‖^2 ∂((volume.restrict (Ioc (0:ℝ) (H:ℝ))).prod μ)):=by
  have hp:MeasurePreserving (fun z:ℝ≥0×Ω=>((z.1:ℝ),z.2))
      (energyMeasure μ H) ((volume.restrict (Ioc (0:ℝ) (H:ℝ))).prod μ):=
    (timeMeasurePreserving H).prod (MeasurePreserving.id μ)
  have hm:Measurable (fun z:ℝ×Ω=>‖Y z‖^2):=hY.norm.pow_const 2
  exact ⟨(hp.integrable_comp hm.aestronglyMeasurable).mpr hi,
    hp.integral_comp (nonnegative_coe_measurableEmbedding.prodMap MeasurableEmbedding.id)
      (fun z:ℝ×Ω=>‖Y z‖^2)⟩
end SHE.NativeRealOutputClock
