module
public import SHE.NativeFourierRowAverage
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeScalarFourierWeight
open MeasureTheory AddCircle StoppedFourier
open scoped NNReal ENNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩

def value (w:ℝ)(a:ℂ→L[ℝ]ℝ)(l:ℤ)(x:HeatCircle):ℝ:=w*a (fourier (-l) x)

theorem measurable (w:ℝ)(a:ℂ→L[ℝ]ℝ)(l:ℤ):Measurable (value w a l):=
  measurable_const.mul (a.continuous.measurable.comp (fourier (-l)).continuous.measurable)

theorem bound (w:ℝ)(a:ℂ→L[ℝ]ℝ)(l:ℤ)(x:HeatCircle):‖value w a l x‖≤‖w‖*‖a‖:=by
  calc
    _=‖w‖*‖a (fourier (-l) x)‖:=norm_mul _ _
    _≤‖w‖*(‖a‖*‖fourier (-l) x‖):=mul_le_mul_of_nonneg_left (a.le_opNorm _) (norm_nonneg _)
    _=‖w‖*‖a‖:=by simp [fourier_apply]

/-- The weighted real/imaginary spatial average is exactly the corresponding
coordinate of the scalar Fourier coefficient, for genuine L1 sections. -/
theorem integral (f:HeatCircle→ℝ)(hf:Integrable f haarAddCircle)(w:ℝ)(a:ℂ→L[ℝ]ℝ)(l:ℤ):
    (∫x:HeatCircle,value w a l x*f x ∂haarAddCircle)=
      w*a (fourierCoeff (fun x:HeatCircle=>(f x:ℂ)) l):=by
  have he:=NativeFourierRowAverage.projection f hf (ContinuousLinearMap.id ℝ ℝ) a l w
  calc
    _=a ((w:ℂ)*fourierCoeff (fun x:HeatCircle=>(f x:ℂ)) l):=by
      simpa only [value,ContinuousLinearMap.id_apply,smul_eq_mul,fourierCoeff] using he.symm
    _=w*a (fourierCoeff (fun x:HeatCircle=>(f x:ℂ)) l):=by
      change a (w • _)=w • a _
      exact map_smul a w _
end SHE.NativeScalarFourierWeight
