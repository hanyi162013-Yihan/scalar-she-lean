module

public import SHEStochastic.NativeSubGaussian
public import SHEStochastic.NativeStoppedGram
public import SHEStochastic.NativeSimpleTransport
public import SHEStochastic.ConditionalBracket

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeBandMoments
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.PastItoInputs SHE.StoppedItoInputs
open scoped NNReal ENNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}
local notation "νin" => FiniteScalarIto.inputMeasure F μ H
local notation "νt" => MathFin.ItoIntegralCLM.timeMeasure_T H

/-- A bounded row has time-band energy at most its squared bound times
the band length. The representatives and both endpoint conventions agree. -/
theorem energy_band_le (u : Process (E := C) F μ H) (M : ℝ≥0)
    (hu : ∀ᵐ p ∂νin, ‖u p‖ ≤ M) {s t : ℝ≥0} (hst : s ≤ t) (htH : t ≤ H) :
    ∀ᵐ ω ∂μ, NativeEnergy.energy (FiniteCylindricalIto.processTransport
      (post F μ H s (stop F μ H t u))) ω ≤ ((t - s) * M ^ 2 : ℝ≥0) := by
  have hrow := NativeStoppedGram.band_transport_ae s t u
  have he := NativeEnergy.energy_ae_of_ae _ _ hrow
  have hp := ae_of_ae_trim F.predictable_le_prod hu
  have hs := (Measure.measurePreserving_swap (μ := μ)
    (ν := MathFin.ItoIntegralCLM.timeMeasure_T H)).quasiMeasurePreserving.ae hp
  filter_upwards [he, Measure.ae_ae_of_ae_prod hs] with ω heω hω
  rw [heω]
  calc
    _ ≤ ∫ r, (Set.Ioc s t).indicator (fun _ ↦ (M : ℝ) ^ 2) r ∂νt := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun r ↦ sq_nonneg _)
        ((integrable_const ((M : ℝ) ^ 2)).indicator measurableSet_Ioc)
      filter_upwards [hω] with r hr
      change ‖(Set.Ioo s t).indicator (fun _ ↦ u (r, ω)) r‖ ^ 2 ≤ _
      by_cases hrt : r ∈ Set.Ioo s t
      · rw [Set.indicator_of_mem hrt, Set.indicator_of_mem (show r ∈ Set.Ioc s t from ⟨hrt.1, hrt.2.le⟩)]
        exact pow_le_pow_left₀ (norm_nonneg _) hr 2
      · rw [Set.indicator_of_notMem hrt, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
        exact Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) r
    _ = _ := by
      rw [HilbertSimplePartition.integral_cell_const s t hst htH]
      simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_sub hst]

/-- Arbitrary native bounded predictable rows have sub-Gaussian integral
increments, uniformly in every deterministic time band. -/
theorem increment_subgaussian (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Process (E := C) F μ H) (M : ℝ≥0) (hu : ∀ᵐ p ∂νin, ‖u p‖ ≤ M)
    {s t : ℝ≥0} (hst : s ≤ t) (htH : t ≤ H) :
    HasSubgaussianMGF
      (fun ω ↦ (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral (stop F μ H t u) ω -
        (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral (stop F μ H s u) ω)
      ((t - s) * M ^ 2) μ := by
  have hsg := NativeSubGaussian.hasSubgaussianMGF P e
    (FiniteCylindricalIto.processTransport (post F μ H s (stop F μ H t u)))
    ((t - s) * M ^ 2) (energy_band_le u M hu hst htH)
  exact hsg.congr (ConditionalBracket.integral_increment
    (FiniteCylindricalIto.terminalIto P.toCoordinates e) hst u)

theorem increment_fourth_le (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Process (E := C) F μ H) (M : ℝ≥0) (hu : ∀ᵐ p ∂νin, ‖u p‖ ≤ M)
    {s t : ℝ≥0} (hst : s ≤ t) (htH : t ≤ H) :
    (∫ ω, ((FiniteCylindricalIto.terminalIto P.toCoordinates e).integral (stop F μ H t u) ω -
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral (stop F μ H s u) ω) ^ 4 ∂μ) ≤
        48 * Real.exp (1 / 2 : ℝ) * (((t - s) * M ^ 2 : ℝ≥0) : ℝ) ^ 2 :=
  SubGaussianFourthMoment.integral_fourth_le (increment_subgaussian P e u M hu hst htH)

end SHEStochastic.NativeBandMoments
