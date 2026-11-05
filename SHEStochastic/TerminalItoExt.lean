module

public import SHE.StandardTerminalIto

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHE.StandardTerminalIto
open MeasureTheory PredictableL2
open scoped NNReal

theorem ext_integral {Ω C : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
    {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} {H : ℝ≥0}
    : Function.Injective (fun I : StandardTerminalIto (C := C) (E := ℝ) F μ H ↦ I.integral) := by
  intro I J h
  cases I with
  | mk Ii Ia Ic =>
    cases J with
    | mk Ji Ja Jc =>
      have he : Ii = Ji := h
      subst Ji
      rfl

end SHE.StandardTerminalIto
