module

public import SHEStochastic.NativeBandMoments
public import SHEStochastic.QuadraticBandError

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section

namespace SHEStochastic.NativeQuadraticBandBounds
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.PastItoInputs SHE.StoppedItoInputs
open scoped NNReal ENNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}
local notation "νin" => FiniteScalarIto.inputMeasure F μ H

/-- The original energy increment lies between zero and its deterministic
band cap; equality of native and original representatives is retained. -/
theorem energy_increment_cap (u : Process (E := C) F μ H) (M : ℝ≥0)
    (hu : ∀ᵐ p ∂νin, ‖u p‖ ≤ M) {s t : ℝ≥0} (hst : s ≤ t) (htH : t ≤ H) :
    ∀ᵐ ω ∂μ, PredictableBracket.energy u t ω - PredictableBracket.energy u s ω ∈
      Set.Icc 0 (((t - s) * M ^ 2 : ℝ≥0) : ℝ) := by
  filter_upwards [NativeBandMoments.energy_band_le u M hu hst htH,
    NativeBoundedNovikov.energy_transport_ae (post F μ H s (stop F μ H t u)),
    PredictableBracket.band_eq_sub u hst] with ω hc ht hb
  change 0 ≤ PredictableBracket.energy u t ω - PredictableBracket.energy u s ω ∧
    PredictableBracket.energy u t ω - PredictableBracket.energy u s ω ≤ _
  rw [← hb]
  refine ⟨integral_nonneg (fun _ ↦ sq_nonneg _), ?_⟩
  rwa [ht] at hc

/-- Centered squared increments have L² error of order the square of
band length for bounded rows. This is a moment bound, not an Itô premise. -/
theorem error_bound (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Process (E := C) F μ H) (M : ℝ≥0) (hu : ∀ᵐ p ∂νin, ‖u p‖ ≤ M)
    {s t : ℝ≥0} (hst : s ≤ t) (htH : t ≤ H) :
    MemLp (QuadraticBandError.error (FiniteCylindricalIto.terminalIto P.toCoordinates e) u s t) 2 μ ∧
      (∫ ω, QuadraticBandError.error (FiniteCylindricalIto.terminalIto P.toCoordinates e) u s t ω ^ 2 ∂μ) ≤
        (96 * Real.exp (1 / 2 : ℝ) + 2) * (((t - s) * M ^ 2 : ℝ≥0) : ℝ) ^ 2 := by
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  let X (ω : Ω) := J.integral (stop F μ H t u) ω - J.integral (stop F μ H s u) ω
  let B (ω : Ω) := PredictableBracket.energy u t ω - PredictableBracket.energy u s ω
  let K : ℝ≥0 := (t - s) * M ^ 2
  have hsg : HasSubgaussianMGF X K μ := NativeBandMoments.increment_subgaussian P e u M hu hst htH
  have hX2 : MemLp (fun ω ↦ X ω ^ 2) 2 μ := by
    have hh := (hsg.memLp (4 : ℝ≥0)).norm_rpow_div (2 : ℝ≥0∞)
    norm_num [Real.rpow_two, Real.norm_eq_abs, sq_abs] at hh
    have hp : (4 : ℝ≥0∞) / 2 = 2 := by
      have he : (4 : ℝ≥0∞) = 2 * 2 := by norm_num
      rw [he, ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)]
    simpa only [hp] using hh
  have hcap : ∀ᵐ ω ∂μ, B ω ∈ Set.Icc 0 (K : ℝ) := energy_increment_cap u M hu hst htH
  have hBsm : AEStronglyMeasurable B μ :=
    (((PredictableBracket.measurable u t).mono (F.le t) le_rfl).stronglyMeasurable.sub
      ((PredictableBracket.measurable u s).mono (F.le s) le_rfl).stronglyMeasurable).aestronglyMeasurable
  have hB2 : MemLp B 2 μ := MemLp.of_bound hBsm (K : ℝ) (hcap.mono fun ω hω ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg hω.1]
    exact hω.2)
  have hE2 : MemLp (QuadraticBandError.error J u s t) 2 μ := hX2.sub hB2
  have hX4i : Integrable (fun ω ↦ X ω ^ 4) μ := by
    convert hX2.integrable_sq using 1
    funext ω
    ring
  have hBsq : (∫ ω, B ω ^ 2 ∂μ) ≤ (K : ℝ) ^ 2 := by
    calc
      _ ≤ ∫ _ω : Ω, (K : ℝ) ^ 2 ∂μ := by
        apply integral_mono_ae hB2.integrable_sq (integrable_const _)
        filter_upwards [hcap] with ω hω
        exact pow_le_pow_left₀ hω.1 hω.2 2
      _ = _ := by simp
  have hXsq : (∫ ω, X ω ^ 4 ∂μ) ≤ 48 * Real.exp (1 / 2 : ℝ) * (K : ℝ) ^ 2 :=
    SubGaussianFourthMoment.integral_fourth_le hsg
  refine ⟨hE2, ?_⟩
  calc
    _ ≤ ∫ ω, 2 * X ω ^ 4 + 2 * B ω ^ 2 ∂μ := by
      apply integral_mono hE2.integrable_sq ((hX4i.const_mul 2).add (hB2.integrable_sq.const_mul 2))
      intro ω
      change (X ω ^ 2 - B ω) ^ 2 ≤ (2 * X ω ^ 4 + 2 * B ω ^ 2)
      nlinarith [sq_nonneg (X ω ^ 2 + B ω)]
    _ = 2 * (∫ ω, X ω ^ 4 ∂μ) + 2 * (∫ ω, B ω ^ 2 ∂μ) := by
      rw [integral_add (hX4i.const_mul 2) (hB2.integrable_sq.const_mul 2),
        integral_const_mul, integral_const_mul]
    _ ≤ _ := by nlinarith

end SHEStochastic.NativeQuadraticBandBounds
