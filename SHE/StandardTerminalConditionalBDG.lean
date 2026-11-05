module

public import SHE.StandardTerminalBDGPower

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE
open MeasureTheory PredictableL2
open scoped NNReal ENNReal

/-- The conditional form of the SAME accepted BDG package3, stated for
events in the initial sigma algebra. No heat or SPDE estimate is part of
this universal stochastic input. -/
def StandardTerminalConditionalBDGPower {Ω C E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup C] [NormedSpace ℝ C] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} {h : ℝ≥0}
    (p : ℕ) (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ h) (B : ℝ≥0) : Prop :=
  ∀ (A : Set Ω), MeasurableSet[𝓕 0] A → ∀ v : Process (E := C) 𝓕 μ h,
    (∫⁻ ω in A, ENNReal.ofReal (‖I.integral v ω‖ ^ (2 * p)) ∂μ) ≤
      (B : ℝ≥0∞) * (∫⁻ ω in A,
        (∫⁻ s, ENNReal.ofReal (‖v (s, ω)‖ ^ 2) ∂timeMeasure h) ^ p ∂μ)

namespace StandardTerminalConditionalBDGPower
variable {Ω C E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} {h : ℝ≥0}

theorem unconditional {p : ℕ} (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ h)
    {B : ℝ≥0} (hBDG : StandardTerminalConditionalBDGPower p I B) :
    StandardTerminalBDGPower p I B := by
  intro v
  simpa only [Measure.restrict_univ] using hBDG Set.univ MeasurableSet.univ v

theorem moment_of_bracket_bound {p : ℕ}
    (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ h) {B : ℝ≥0}
    (hBDG : StandardTerminalConditionalBDGPower p I B) (A : Set Ω) (hA : MeasurableSet[𝓕 0] A)
    (v : Process (E := C) 𝓕 μ h) {K : ℝ} (hK : 0 ≤ K)
    (hbr : ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal (‖v (s, ω)‖ ^ 2) ∂timeMeasure h) ≤ ENNReal.ofReal K) :
    (∫⁻ ω in A, ENNReal.ofReal (‖I.integral v ω‖ ^ (2 * p)) ∂μ) ≤
      ENNReal.ofReal ((B : ℝ) * K ^ p) * μ A := by
  have hp : (∫⁻ ω in A, (∫⁻ s, ENNReal.ofReal (‖v (s, ω)‖ ^ 2) ∂timeMeasure h) ^ p ∂μ) ≤
      (ENNReal.ofReal K) ^ p * μ A := by
    have hh := lintegral_mono_ae
      ((ae_restrict_of_ae (s := A) hbr).mono (fun _ hω => pow_le_pow_left₀ (by simp) hω p))
    simpa only [lintegral_const, Measure.restrict_apply_univ] using hh
  calc
    _ ≤ (B : ℝ≥0∞) * (∫⁻ ω in A,
        (∫⁻ s, ENNReal.ofReal (‖v (s, ω)‖ ^ 2) ∂timeMeasure h) ^ p ∂μ) := hBDG A hA v
    _ ≤ (B : ℝ≥0∞) * ((ENNReal.ofReal K) ^ p * μ A) := mul_le_mul_right hp _
    _ = _ := by
      rw [← ENNReal.ofReal_pow hK, ← mul_assoc,
        show (B : ℝ≥0∞) = ENNReal.ofReal (B : ℝ) by simp]
      congr 1
      exact (ENNReal.ofReal_mul B.2).symm

end StandardTerminalConditionalBDGPower
end SHE
