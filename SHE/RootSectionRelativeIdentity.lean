module
public import SHE.RootSectionAverage
public import SHE.RootHistoryFubini
public import SHE.ForestTranslation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.RootSectionRelativeIdentity
open MeasureTheory Set StoppedFourier CutoffWordLevel CutoffWordHistories HistoryProductMeasure
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {Ω:Type*}[MeasurableSpace Ω]

/-- Translating every old spatial coordinate by the retained root does
not change the average under the original product Haar measure. This is
an exact change of variables, without an integrability assumption. -/
theorem eq (R:ReferenceData)(k:ℕ)(F:Ω×History HeatCircle k→ℝ)(z:Ω×HeatCircle):
    HistoryProductMeasure.rootAverage R k F z=RootSectionAverage.average R k F z:=by
  unfold HistoryProductMeasure.rootAverage RootSectionAverage.average
  apply integral_congr_ae
  apply ae_of_all
  intro t
  exact (OrderedHeatForests.relativeShift_preserving k z.2).integral_comp'
    (fun w=>F (z.1,separated k (z.2,t,w)))
end SHE.RootSectionRelativeIdentity
