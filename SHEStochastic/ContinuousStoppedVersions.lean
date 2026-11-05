module
public import SHE.StandardItoStoppedParameterFubini

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped NNReal

namespace SHEStochastic

/-- Ordinary continuous versions for one integrand at a time. This
predicate is an intermediate reduction, not an additional accepted axiom. -/
def ContinuousStoppedVersions {Ω C : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup C] [InnerProductSpace ℝ C]
    {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} {H : ℝ≥0}
    (J : SHE.StandardTerminalIto (C := C) (E := ℝ) F μ H) : Prop :=
  ∀ v : SHE.PredictableL2.Process (E := C) F μ H, ∃ U : ℝ≥0 → Ω → ℝ,
    (∀ ω, Continuous (fun t ↦ U t ω)) ∧
    (∀ q : ℝ≥0, ∀ᵐ ω ∂μ,
      U q ω = J.integral (SHE.StoppedItoInputs.stop (C := C) F μ H (q : ℝ) v) ω)

end SHEStochastic
