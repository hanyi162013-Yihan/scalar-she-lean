module

public import SHE.TimeDilationInverseIto

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.PredictableTimeDilation
open MeasureTheory PredictableL2
open scoped NNReal
variable {Ω C E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ]
variable (c : ℝ≥0) (hc : 0<c) (h : ℝ≥0)

omit [SFinite μ] in
theorem terminalIto_eq_of_integral_eq
    (I J : StandardTerminalIto (C:=C) (E:=E) 𝓕 μ h) (he : I.integral=J.integral) : I=J := by
  cases I
  cases J
  cases he
  rfl

/-- The deterministic clock round trip recovers the original complete
Itô structure exactly. Its ordinary adaptedness and centering proofs
are propositionally irrelevant; the actual linear integral is equal. -/
theorem integral_inverseIntegral_eq
    (J : StandardTerminalIto (C:=C) (E:=E) (filtration 𝓕 (clock c hc)) μ (c*h)) :
    integral 𝓕 μ c hc h (inverseIntegral 𝓕 μ c hc h J)=J := by
  apply terminalIto_eq_of_integral_eq
  apply DFunLike.ext
  intro v
  exact integral_inverseIntegral 𝓕 μ c hc h J v

end SHE.PredictableTimeDilation
