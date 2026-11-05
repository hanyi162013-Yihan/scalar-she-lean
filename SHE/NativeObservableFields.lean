module
public import SHE.JointInterpolationFields
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 600000
namespace SHE.NativeHeatObservation
open MeasureTheory DyadicApproximation StoppedFourier
local instance nativeObservableFields_realSigma : MeasurableSpace RealL2:=borel _
local instance nativeObservableFields_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance nativeObservableFields_period : Fact (0<2*Real.pi):=⟨by positivity⟩
attribute [local irreducible] functional

/-- Borel substitution into the actual native heat functional,
including the specified nonpositive-age extension. -/
theorem observable_measurable {W:Type*} [MeasurableSpace W]
    {U:W→RealL2} (hU:Measurable U) {t:W→ℝ} (ht:Measurable t)
    {x:W→HeatCircle} (hx:Measurable x):
    Measurable (fun w=>functional (t w) (x w) (U w)):=by
  have harg:Measurable (fun w=>(U w,(t w,x w))):=hU.prodMk (ht.prodMk hx)
  exact functional_joint_measurable.comp harg

end SHE.NativeHeatObservation
