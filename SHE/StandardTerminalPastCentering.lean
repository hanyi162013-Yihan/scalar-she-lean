module

public import SHE.StandardTerminalPastLocality

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.StandardTerminalPastLocality
open MeasureTheory Set PredictableL2 PastItoInputs
open scoped NNReal ENNReal
variable {Ω C E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} {H : ℝ≥0}

/-- Genuine conditional centering of a post-v stochastic integral,
expressed on every event in the actual past sigma algebra. This follows
from the same ordinary event pullout and unconditional centering. -/
theorem centered_on_past_event (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ H)
    (hlocal : StandardTerminalPastLocality I) (v : ℝ≥0) (A : Set Ω)
    (hA : MeasurableSet[𝓕 v] A) (u : Process (E := C) 𝓕 μ H) :
    (∫ ω in A,I.integral (post 𝓕 μ H v u) ω ∂μ)=0 := by
  rw [← integral_indicator (𝓕.le v A hA)]
  exact (integral_congr_ae (hlocal v A hA u)).symm.trans (I.centered _)

end SHE.StandardTerminalPastLocality
