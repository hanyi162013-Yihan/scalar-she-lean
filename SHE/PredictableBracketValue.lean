module

public import SHE.PredictableL2

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.PredictableL2
open MeasureTheory
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω] [NormedAddCommGroup C]
variable {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} {H : ℝ≥0}

/-- The literal pathwise integrated squared norm of a predictable L2
input. This definition is independent of any stochastic integral. -/
def bracket (u : Process (E := C) 𝓕 μ H) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ s : ℝ≥0,ENNReal.ofReal (‖u (s,ω)‖^2) ∂timeMeasure H

end SHE.PredictableL2
