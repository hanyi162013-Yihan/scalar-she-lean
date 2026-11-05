module

public import SHEStochastic.FiniteCylindricalStopped
public import SHEStochastic.StandardItoStoppedParameterFubini

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.FiniteCylindricalIto
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω ι C : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)

/-- Ordinary continuous versions of every stopped native cylindrical
integral. The countable-coordinate approximation adds no stochastic input. -/
theorem continuousStoppedVersions : ContinuousStoppedVersions (terminalIto P.toCoordinates e) := by
  classical
  intro v
  obtain ⟨X, hX, hC⟩ := exists_continuous_modification P e (processTransport v)
  let Z (t : ℝ≥0) (ω : Ω) := X (min t H) ω
  have hZc : ∀ᵐ ω ∂μ, Continuous (fun t ↦ Z t ω) := by
    filter_upwards [hC] with ω hω
    exact hω.comp_continuous (continuous_id.min continuous_const)
      (fun t ↦ ⟨zero_le, min_le_right t H⟩)
  have hZrep (q : ℝ≥0) : ∀ᵐ ω ∂μ,
      Z q ω = (terminalIto P.toCoordinates e).integral (StoppedItoInputs.stop F μ H q v) ω := by
    rw [stopped_eq_prefix_min]
    exact hX (min q H) (min_le_right q H)
  let U (t : ℝ≥0) (ω : Ω) := if Continuous (fun s ↦ Z s ω) then Z t ω else 0
  have hUc (ω : Ω) : Continuous (fun t ↦ U t ω) := by
    by_cases hω : Continuous (fun s ↦ Z s ω)
    · simpa only [U, if_pos hω] using hω
    · simpa only [U, if_neg hω] using (continuous_const : Continuous (fun _ : ℝ≥0 ↦ (0 : ℝ)))
  refine ⟨U, hUc, fun q ↦ ?_⟩
  filter_upwards [hZc, hZrep q] with ω hc hr
  exact (if_pos hc).trans hr

/-- The ENTIRE original stopped-parameter interface for the native
finite-horizon cylindrical integral, including joint predictability and
one simultaneous continuous time version for almost every parameter. -/
theorem stoppedParameterFubini : StandardItoStoppedParameterFubini (terminalIto P.toCoordinates e) := by
  apply standardItoStoppedParameterFubini_of_continuousVersions
  intro _
  exact continuousStoppedVersions P e

end SHEStochastic.FiniteCylindricalIto
