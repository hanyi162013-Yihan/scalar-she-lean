module

public import SHE.HistoryRelativeSample

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace SHE.HistoryProductMeasure
open Set MeasureTheory AddCircle StoppedFourier CutoffWordLevel CutoffWordHistories
local instance rootHistoryMeasure_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]

/-- Disintegrate the original history measure with the sample and
output root OUTSIDE the original old-time/old-space product. -/
theorem rootSample_preserving (R : ReferenceData) (μ : Measure Ω) [SFinite μ] (k : ℕ) :
    MeasurePreserving
      (fun z : (Ω×HeatCircle)×((Fin k→ℝ)×(Fin k→HeatCircle))=>
        (z.1.1,separated k (z.1.2,z.2.1,fun i=>z.2.2 i+z.1.2)))
      ((μ.prod haarAddCircle).prod ((Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))).prod
        (Measure.pi (fun _ : Fin k=>haarAddCircle))))
      (μ.prod (historyMeasure R haarAddCircle k)) := by
  let Y:=μ.prod (haarAddCircle : Measure HeatCircle)
  let T:=Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))
  let W:=Measure.pi (fun _ : Fin k=>haarAddCircle (T:=2*Real.pi))
  have h₁:=(measurePreserving_prodAssoc Y T W).symm
  have h₂:=(Measure.measurePreserving_swap (μ:=Y) (ν:=T)).prod (MeasurePreserving.id W)
  have h₃:=measurePreserving_prodAssoc T Y W
  convert! (relativeSample_preserving R μ k).comp (h₃.comp (h₂.comp h₁)) using 1

/-- The interpolation parameter can be moved inside while the sample
and original output remain outside. This exact measure identity is
the Fubini bridge for root-retained three-leg FTCs. -/
theorem rootTheta_preserving (R : ReferenceData) (τ : Measure Θ) [SFinite τ]
    (μ : Measure Ω) [SFinite μ] (k : ℕ) :
    MeasurePreserving
      (fun z : (Ω×HeatCircle)×(Θ×((Fin k→ℝ)×(Fin k→HeatCircle)))=>
        (z.2.1,(z.1.1,separated k (z.1.2,z.2.2.1,fun i=>z.2.2.2 i+z.1.2))))
      ((μ.prod haarAddCircle).prod (τ.prod
        ((Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))).prod
          (Measure.pi (fun _ : Fin k=>haarAddCircle)))))
      (τ.prod (μ.prod (historyMeasure R haarAddCircle k))) := by
  let Y:=μ.prod (haarAddCircle : Measure HeatCircle)
  let B:=(Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))).prod
    (Measure.pi (fun _ : Fin k=>haarAddCircle (T:=2*Real.pi)))
  have h₁:=(measurePreserving_prodAssoc Y τ B).symm
  have h₂:=(Measure.measurePreserving_swap (μ:=Y) (ν:=τ)).prod (MeasurePreserving.id B)
  have h₃:=measurePreserving_prodAssoc τ Y B
  convert! ((MeasurePreserving.id τ).prod (rootSample_preserving R μ k)).comp
    (h₃.comp (h₂.comp h₁)) using 1

end SHE.HistoryProductMeasure
