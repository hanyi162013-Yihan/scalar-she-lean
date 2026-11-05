module

public import SHEStochastic.WeightedBracketBound
public import SHE.StandardTerminalBDGPower

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.BDGRealMoments
open MeasureTheory SHE SHE.PredictableL2 Filter
open scoped NNReal ENNReal

variable {Ω C E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

theorem bracket_moment_eq (p : ℕ) (u : Process (E := C) F μ H)
    (hA : Integrable (fun ω ↦ StochasticExponential.bracket F μ H u ω ^ p) μ) :
    (∫⁻ ω, (∫⁻ r, ENNReal.ofReal (‖u (r, ω)‖ ^ 2) ∂timeMeasure H) ^ p ∂μ) =
      ENNReal.ofReal (∫ ω, StochasticExponential.bracket F μ H u ω ^ p ∂μ) := by
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (StochasticExponential.bracket F μ H u ω ^ p) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [WeightedBracketBound.lintegral_eq u] with ω hω
      rw [hω, ENNReal.ofReal_pow (WeightedBracketBound.bracket_nonneg u ω)]
    _ = _ := (ofReal_integral_eq_lintegral_ofReal hA
      (Eventually.of_forall fun ω ↦ pow_nonneg (WeightedBracketBound.bracket_nonneg u ω) p)).symm

/-- The converse conversion for inputs whose two moments are finite. -/
theorem of_real_bound (p : ℕ) (I : StandardTerminalIto (C := C) (E := E) F μ H)
    (B : ℝ≥0) (u : Process (E := C) F μ H)
    (hOut : Integrable (fun ω ↦ ‖I.integral u ω‖ ^ (2 * p)) μ)
    (hA : Integrable (fun ω ↦ StochasticExponential.bracket F μ H u ω ^ p) μ)
    (hb : (∫ ω, ‖I.integral u ω‖ ^ (2 * p) ∂μ) ≤
      (B : ℝ) * ∫ ω, StochasticExponential.bracket F μ H u ω ^ p ∂μ) :
    (∫⁻ ω, ENNReal.ofReal (‖I.integral u ω‖ ^ (2 * p)) ∂μ) ≤
      (B : ℝ≥0∞) * ∫⁻ ω, (∫⁻ r, ENNReal.ofReal (‖u (r, ω)‖ ^ 2) ∂timeMeasure H) ^ p ∂μ := by
  rw [bracket_moment_eq p u hA, ← ofReal_integral_eq_lintegral_ofReal hOut
    (Eventually.of_forall fun _ ↦ pow_nonneg (norm_nonneg _) _)]
  refine (ENNReal.ofReal_le_ofReal hb).trans_eq ?_
  exact (ENNReal.ofReal_mul B.property).trans (by simp)

/-- The original extended-valued BDG statement gives an ordinary real
moment estimate whenever its bracket moment is finite. Finiteness of
the output moment is proved here, not silently assumed. -/
theorem bound (p : ℕ) (I : StandardTerminalIto (C := C) (E := E) F μ H)
    (B : ℝ≥0) (hBDG : StandardTerminalBDGPower p I B)
    (u : Process (E := C) F μ H)
    (hA : Integrable (fun ω ↦ StochasticExponential.bracket F μ H u ω ^ p) μ) :
    Integrable (fun ω ↦ ‖I.integral u ω‖ ^ (2 * p)) μ ∧
      (∫ ω, ‖I.integral u ω‖ ^ (2 * p) ∂μ) ≤
        (B : ℝ) * ∫ ω, StochasticExponential.bracket F μ H u ω ^ p ∂μ := by
  have hR := bracket_moment_eq p u hA
  have hbn : 0 ≤ ∫ ω, StochasticExponential.bracket F μ H u ω ^ p ∂μ :=
    integral_nonneg fun ω ↦ pow_nonneg (WeightedBracketBound.bracket_nonneg u ω) p
  have hbound : (∫⁻ ω, ENNReal.ofReal (‖I.integral u ω‖ ^ (2 * p)) ∂μ) ≤
      ENNReal.ofReal ((B : ℝ) * ∫ ω, StochasticExponential.bracket F μ H u ω ^ p ∂μ) := by
    have hh := hBDG u
    rw [hR] at hh
    calc
      _ ≤ (B : ℝ≥0∞) * ENNReal.ofReal (∫ ω, StochasticExponential.bracket F μ H u ω ^ p ∂μ) := hh
      _ = _ := by
        rw [show (B : ℝ≥0∞) = ENNReal.ofReal (B : ℝ) by simp]
        exact (ENNReal.ofReal_mul B.property).symm
  have hOut : Integrable (fun ω ↦ ‖I.integral u ω‖ ^ (2 * p)) μ := by
    refine ⟨((Lp.stronglyMeasurable _).norm.pow (2 * p)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ ↦ pow_nonneg (norm_nonneg _) _)]
    exact hbound.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hOut, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hOut
    (Eventually.of_forall fun _ ↦ pow_nonneg (norm_nonneg _) _)] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg B.property hbn)).mp hbound

end SHEStochastic.BDGRealMoments
