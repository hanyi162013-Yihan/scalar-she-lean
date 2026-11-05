module

public import SHEStochastic.NativeRandomStopLocality
public import SHE.StoppedInputAlgebra

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.NativeStoppedInputComparison
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal
variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (H : ℝ≥0)

/-- Random-stop locality for two arbitrary integrands, observed through
their deterministic-time stopped Itô integrals. -/
theorem integral_eq_before (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (hlocal : StandardTerminalPastLocality J) (hversions : ContinuousStoppedVersions J)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (u v : Process (E := C) F μ H) (T : ℝ≥0)
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime F τ)
    (huv : ∀ᵐ p ∂energyMeasure μ H, (p.1 : WithTop ℝ≥0) < τ p.2 → u p = v p) :
    ∀ᵐ ω ∂μ, (T : WithTop ℝ≥0) ≤ τ ω →
      J.integral (StoppedItoInputs.stop F μ H T u) ω =
      J.integral (StoppedItoInputs.stop F μ H T v) ω := by
  let uT := StoppedItoInputs.stop F μ H T u
  let vT := StoppedItoInputs.stop F μ H T v
  have hUV : ∀ᵐ p ∂energyMeasure μ H,
      (p.1 : WithTop ℝ≥0) < τ p.2 → uT p = vT p := by
    filter_upwards [huv, StoppedItoInputs.stop_ae F μ H T u,
      StoppedItoInputs.stop_ae F μ H T v] with p hp hu hv htime
    rw [hu,hv]
    by_cases hpt : p ∈ StoppedItoInputs.before (Ω := Ω) T
    · rw [Set.indicator_of_mem hpt,Set.indicator_of_mem hpt,hp htime]
    · rw [Set.indicator_of_notMem hpt,Set.indicator_of_notMem hpt]
  exact NativeRandomStopLocality.integral_eq_before F μ H J hlocal hversions hnull
    uT vT T (by simp only [uT,StoppedInputAlgebra.stop_stop,min_self])
    (by simp only [vT,StoppedInputAlgebra.stop_stop,min_self]) τ hτ hUV

end SHEStochastic.NativeStoppedInputComparison
