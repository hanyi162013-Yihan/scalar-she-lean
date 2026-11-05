module
public import SHE.RootSectionAverage
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.RootSectionZero
open MeasureTheory StoppedFourier CutoffWordHistories
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {Ω:Type*}[MeasurableSpace Ω]

/-- An empty original history average retains exactly its root value. -/
theorem average (R:CutoffWordLevel.ReferenceData)(F:Ω×HeatCircle→ℝ)(ω:Ω)(x:HeatCircle):
    RootSectionAverage.average R 0 F (ω,x)=F (ω,x):=by
  have hi:Integrable (fun h:History HeatCircle 0=>F (ω,h))
      (historyMeasure R (Measure.dirac x) 0):=by
    change Integrable (fun h:HeatCircle=>F (ω,h)) (Measure.dirac x)
    exact integrable_dirac (a:=x) (f:=fun h:HeatCircle=>F (ω,h)) (by finiteness)
  have he:=RootSectionAverage.integral_dirac_history R 0 x (fun h=>F (ω,h)) hi
  change (∫p:HeatCircle,F (ω,p) ∂Measure.dirac x)=RootSectionAverage.average R 0 F (ω,x) at he
  rw [integral_dirac] at he
  exact he.symm
end SHE.RootSectionZero
