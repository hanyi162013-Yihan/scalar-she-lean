module
public import SHE.NativeJointGammaCurrent
public import SHE.NativeScalarFieldAlgebra
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.NativeJointCurrentEndpoint
open MeasureTheory NativeHeatObservation DyadicApproximation StoppedFourier
open scoped NNReal ENNReal
variable {Ω:Type*}

theorem state (U V:ℝ≥0×Ω→RealL2)(Λ θ:ℝ)(b:ℝ≥0)(ω:Ω):
    NativeJointGammaCurrent.state U V Λ θ b (b,ω)=U (b,ω)+θ • (V (b,ω)-U (b,ω)):=by
  simp only [NativeJointGammaCurrent.state,sub_self,mul_zero,Real.exp_zero,one_smul,
    heat,zero_div,RealHeat.realHeat_zero,ContinuousLinearMap.id_apply]

theorem scalar_zero (U V:ℝ≥0×Ω→RealL2)(Λ:ℝ)(b:ℝ≥0)(ω:Ω)(x:HeatCircle):
    PredictableScalarField.nativeField (NativeJointGammaCurrent.state U V Λ 0 b) ((b,ω),x)=
      PredictableScalarField.nativeField U ((b,ω),x):=by
  apply NativeScalarFieldAlgebra.congr
  rw [state,zero_smul,add_zero]

theorem scalar_one (U V:ℝ≥0×Ω→RealL2)(Λ:ℝ)(b:ℝ≥0)(ω:Ω)(x:HeatCircle):
    PredictableScalarField.nativeField (NativeJointGammaCurrent.state U V Λ 1 b) ((b,ω),x)=
      PredictableScalarField.nativeField V ((b,ω),x):=by
  apply NativeScalarFieldAlgebra.congr
  rw [state,one_smul,add_sub_cancel]

end SHE.NativeJointCurrentEndpoint
