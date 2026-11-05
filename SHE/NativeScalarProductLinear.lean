module
public import SHE.NativeScalarProductAlgebra
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.NativeScalarProductLinear
open MeasureTheory AddCircle StoppedFourier DyadicApproximation
open scoped NNReal ENNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : MeasurableSpace RealL2:=borel _
local instance : BorelSpace RealL2:=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω](μ:Measure Ω)[SFinite μ]

theorem smul_ae (a:ℝ)(U:Ω→RealL2)(hU:Measurable U):
    ∀ᵐx:HeatCircle∂haarAddCircle,∀ᵐω∂μ,
      PredictableScalarField.nativeField (fun ω=>a • U ω) (ω,x)=
        a*PredictableScalarField.nativeField U (ω,x):=by
  have he:MeasurableSet {p:Ω×HeatCircle|
      PredictableScalarField.nativeField (fun ω=>a • U ω) p=a*PredictableScalarField.nativeField U p}:=
    measurableSet_eq_fun (PredictableScalarField.nativeField_measurable (hU.const_smul a))
      ((PredictableScalarField.nativeField_measurable hU).const_mul a)
  apply (Measure.ae_ae_comm he).mp
  apply ae_of_all
  intro ω
  have hs:=(CircleNormalization.scale_measurePreserving (2*Real.pi) 1).quasiMeasurePreserving.ae
    (Lp.coeFn_smul a (U ω))
  filter_upwards [hs,PredictableScalarField.nativeField_ae_unit (fun ω=>a • U ω) ω,
    PredictableScalarField.nativeField_ae_unit U ω] with x hs hl hr
  rw [hl,hr,hs]
  rfl

theorem add_smul_ae (a:ℝ)(U V:Ω→RealL2)(hU:Measurable U)(hV:Measurable V):
    ∀ᵐx:HeatCircle∂haarAddCircle,∀ᵐω∂μ,
      PredictableScalarField.nativeField (fun ω=>U ω+a • V ω) (ω,x)=
        PredictableScalarField.nativeField U (ω,x)+a*PredictableScalarField.nativeField V (ω,x):=by
  filter_upwards [NativeScalarProductAlgebra.add_ae μ U (fun ω=>a • V ω) hU (hV.const_smul a),
    smul_ae μ a V hV] with x ha hs
  filter_upwards [ha,hs] with ω ha hs
  rw [ha,hs]

end SHE.NativeScalarProductLinear
