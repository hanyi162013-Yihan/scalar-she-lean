module
public import SHE.MovingCanonicalFrozenRows
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace SHE.JointPredictableDiagonal
open MeasureTheory StoppedFourier MovingCanonicalFrozenRows
open scoped NNReal
variable {Ω:Type*}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)

def diagonal (Y:Parameters×(ℝ≥0×Ω)→ℝ) (z:(ℝ×(ℝ≥0×Ω))×HeatCircle):ℝ:=
  Y ((z.1.1,(z.1.2.1,z.2)),z.1.2)

/-- Diagonal evaluation at the current clock preserves genuine
parameter/predictability. It is applied to a joint predictable version,
rather than to a merely ambient-Borel family of separate versions. -/
theorem predictable {Y:Parameters×(ℝ≥0×Ω)→ℝ}
    (hY:StronglyMeasurable[((inferInstance:MeasurableSpace Parameters).prod 𝓕.predictable)] Y):
    @Measurable ((ℝ×(ℝ≥0×Ω))×HeatCircle) ℝ
      (((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable).prod inferInstance) _ (diagonal Y):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have ht:Measurable (fun z:(ℝ×(ℝ≥0×Ω))×HeatCircle=>z.1.2.1):=
    (PredictableClock.time_measurable 𝓕).comp measurable_fst.snd
  have hp:Measurable (fun z:(ℝ×(ℝ≥0×Ω))×HeatCircle=>(z.1.1,(z.1.2.1,z.2))):=
    measurable_fst.fst.prodMk (ht.prodMk measurable_snd)
  exact (hY.comp_measurable (hp.prodMk measurable_fst.snd)).measurable
end SHE.JointPredictableDiagonal
