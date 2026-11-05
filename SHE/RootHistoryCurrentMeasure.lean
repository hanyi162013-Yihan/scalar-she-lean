module
public import SHE.HistoryProductMeasure
public import SHE.ProductIntegralCycle
public import SHE.NodeIntegralCycle
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.RootHistoryCurrentMeasure
open Set MeasureTheory AddCircle StoppedFourier CutoffWordLevel CutoffWordHistories HistoryProductMeasure
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {Q:Type*}[MeasurableSpace Q]

/-- Exact original old-time/current-time/root/old-space disintegration.
The current law is retained as a separate original parameter measure. -/
theorem preserving (R:ReferenceData)(k:ℕ)(ν:Measure Q)[SFinite ν]:
    MeasurePreserving
      (fun z:(((Fin k→ℝ)×Q)×HeatCircle)×(Fin k→HeatCircle)=>
        (separated k (z.1.2,z.1.1.1,z.2),z.1.1.2))
      ((((Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon))).prod ν).prod
        (haarAddCircle:Measure HeatCircle)).prod (Measure.pi (fun _:Fin k=>haarAddCircle)))
      ((historyMeasure R haarAddCircle k).prod ν):=by
  let T:=Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon))
  let W:=Measure.pi (fun _:Fin k=>haarAddCircle (T:=2*Real.pi))
  let X:Measure HeatCircle:=haarAddCircle
  have h₁:=((Measure.measurePreserving_swap (μ:=T) (ν:=ν)).prod (MeasurePreserving.id X)).prod
    (MeasurePreserving.id W)
  have h₂:=(NodeIntegralCycle.measurePreserving_cycle ν T X).prod (MeasurePreserving.id W)
  have h₃:=((Measure.measurePreserving_swap (μ:=ν) (ν:=X)).prod (MeasurePreserving.id T)).prod
    (MeasurePreserving.id W)
  have h₄:=MeasurePreserving.symm
    (ProductIntegralCycle.cycle (A:=HeatCircle) (T:=Fin k→ℝ) (C:=Fin k→HeatCircle) (Ω:=Q))
    (ProductIntegralCycle.measurePreserving_cycle X T W ν)
  have h₅:=(separated_measurePreserving R X k).prod (MeasurePreserving.id ν)
  convert! h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁))) using 1

end SHE.RootHistoryCurrentMeasure
