module

public import SHE.NativeScalarFieldAlgebra
public import SHE.JointInterpolationFields

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
namespace SHE.NativeScalarProductAlgebra
open MeasureTheory AddCircle StoppedFourier DyadicApproximation NativeHeatObservation
local instance nativeScalarProductAlgebra_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeScalarProductAlgebra_realSigma : MeasurableSpace RealL2:=borel _
local instance nativeScalarProductAlgebra_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance nativeScalarProductAlgebra_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeScalarProductAlgebra_circleSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance nativeScalarProductAlgebra_realSecond : SecondCountableTopology RealL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]

theorem add_ae (U V : Ω→RealL2) (hU : Measurable U) (hV : Measurable V) :
    ∀ᵐ x : HeatCircle∂haarAddCircle,∀ᵐ ω∂μ,
      PredictableScalarField.nativeField (fun ω=>U ω+V ω) (ω,x)=
        PredictableScalarField.nativeField U (ω,x)+PredictableScalarField.nativeField V (ω,x) := by
  have hme : MeasurableSet {p : Ω×HeatCircle|
      PredictableScalarField.nativeField (fun ω=>U ω+V ω) p=
        PredictableScalarField.nativeField U p+PredictableScalarField.nativeField V p}:=
    measurableSet_eq_fun (PredictableScalarField.nativeField_measurable (hU.add hV))
      ((PredictableScalarField.nativeField_measurable hU).add (PredictableScalarField.nativeField_measurable hV))
  exact (Measure.ae_ae_comm hme).mp (ae_of_all _ (NativeScalarFieldAlgebra.add U V))

theorem heat_ae (U : Ω→RealL2) (hU : Measurable U) {τ : ℝ} (hτ : 0<τ) :
    ∀ᵐ x : HeatCircle∂haarAddCircle,∀ᵐ ω∂μ,
      PredictableScalarField.nativeField (fun ω=>heat τ (U ω)) (ω,x)=functional τ x (U ω) := by
  have hheat : Measurable (fun ω=>heat τ (U ω)):=(heat τ).continuous.measurable.comp hU
  have hleft:=PredictableScalarField.nativeField_measurable hheat
  have harg : Measurable (fun p : Ω×HeatCircle=>(U p.1,(τ,p.2))):=
    (hU.comp measurable_fst).prodMk (measurable_const.prodMk measurable_snd)
  have hright:=functional_joint_measurable.comp harg
  have hme:=measurableSet_eq_fun hleft hright
  apply (Measure.ae_ae_comm hme).mp
  exact ae_of_all _ (fun ω=>(NativeHeatFunctionalEnergy.functional_ae hτ (U ω)).symm)

end SHE.NativeScalarProductAlgebra
