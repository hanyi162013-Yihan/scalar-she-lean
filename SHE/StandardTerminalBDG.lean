module

public import SHE.StandardTerminalIto

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE
open MeasureTheory PredictableL2
open scoped NNReal ENNReal

/-- Accepted stochastic input package 3, specialized to one fixed even
moment. This is the universal Hilbert martingale BDG inequality for the
ordinary terminal integral. No heat kernel, time increment or SPDE
estimate is included in this standard input. -/
def StandardTerminalBDG16 {Ω C E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} {h : ℝ≥0}
    (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ h) (B : ℝ≥0) : Prop :=
  ∀ v : Process (E := C) 𝓕 μ h,
    (∫⁻ ω,ENNReal.ofReal (‖I.integral v ω‖^16) ∂μ) ≤
      (B:ℝ≥0∞)*(∫⁻ ω,(∫⁻ s,ENNReal.ofReal (‖v (s,ω)‖^2) ∂timeMeasure h)^8 ∂μ)

end SHE
