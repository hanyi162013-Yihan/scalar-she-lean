module

public import SHEStochastic.SquareCompensator
public import SHEStochastic.ConditionalOrthogonalSums

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.QuadraticBandError
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedItoInputs
open scoped NNReal ENNReal

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

def error (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (u : Process (E := C) F μ H) (s t : ℝ≥0) (ω : Ω) : ℝ :=
  (J.integral (stop F μ H t u) ω - J.integral (stop F μ H s u) ω) ^ 2 -
    (PredictableBracket.energy u t ω - PredictableBracket.energy u s ω)

/-- The actual squared increment minus its actual time-energy increment
is conditionally centered in the full original past. -/
theorem centered (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (hlocal : StandardTerminalPastLocality J) (u : Process (E := C) F μ H)
    {s t : ℝ≥0} (hst : s ≤ t) :
    μ[error J u s t | F s] =ᵐ[μ] (fun _ ↦ 0) := by
  have hI : MemLp (fun ω ↦ J.integral (stop F μ H t u) ω -
      J.integral (stop F μ H s u) ω) 2 μ := (Lp.memLp _).sub (Lp.memLp _)
  have hB := (PredictableBracket.integrable u t).sub (PredictableBracket.integrable u s)
  have hv := (ConditionalBracket.condExp_increment_second J hlocal hst u).trans
    (condExp_congr_ae (PredictableBracket.band_eq_sub u hst))
  refine (condExp_sub hI.integrable_sq hB (F s)).trans ?_
  filter_upwards [hv] with ω hω
  change (μ[(fun ω ↦ (J.integral (stop F μ H t u) ω -
      J.integral (stop F μ H s u) ω) ^ 2) | F s]) ω -
    (μ[(fun ω ↦ PredictableBracket.energy u t ω - PredictableBracket.energy u s ω) | F s]) ω = 0
  rw [hω, sub_self]

/-- The same quadratic error is measurable in the past at the right
endpoint, up to the original probability's null sets. -/
theorem adapted (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (u : Process (E := C) F μ H) {s t : ℝ≥0} (hst : s ≤ t) :
    AEStronglyMeasurable[F t] (error J u s t) μ := by
  have hM (r : ℝ≥0) : AEStronglyMeasurable[F r]
      (J.integral (stop F μ H r u) : Ω → ℝ) μ := by
    obtain ⟨Z, hZ, hrep⟩ := stopped_integral_adapted F μ H J r u
    exact hZ.aestronglyMeasurable.congr hrep.symm
  exact ((hM t).sub ((hM s).mono (F.mono hst))).pow 2 |>.sub
    (((PredictableBracket.measurable u t).stronglyMeasurable.aestronglyMeasurable).sub
      (((PredictableBracket.measurable u s).stronglyMeasurable.aestronglyMeasurable).mono (F.mono hst)))

end SHEStochastic.QuadraticBandError
