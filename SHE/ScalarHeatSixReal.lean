module
public import SHE.ScalarHeatSixFields
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.ScalarHeatSixReal
open StoppedFourier
local instance scalarHeatSixReal_period : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {X:Type*}
theorem im (a:ℝ→ℝ)(j:ℕ)(σ0 σ1 z0 z1 m0 m1:X×HeatCircle→ℝ)
    (i:Fin 6)(p:X×HeatCircle):
    (ScalarHeatSixFields.fields a j σ0 σ1 z0 z1 m0 m1 i p).im=0:=by
  fin_cases i <;> rfl
end SHE.ScalarHeatSixReal
