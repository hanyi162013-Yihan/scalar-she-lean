module

public import SHE.PredictableItoRotation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE
open MeasureTheory PredictableL2
open scoped NNReal ENNReal

/-- The same accepted stochastic input package3 at an arbitrary fixed
even moment2p. No heat kernel, convolution or SPDE estimate is included. -/
def StandardTerminalBDGPower {Ω C E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup C] [NormedSpace ℝ C] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} {h : ℝ≥0}
    (p : ℕ) (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ h) (B : ℝ≥0) : Prop :=
  ∀ v : Process (E := C) 𝓕 μ h,
    (∫⁻ ω, ENNReal.ofReal (‖I.integral v ω‖ ^ (2 * p)) ∂μ) ≤
      (B : ℝ≥0∞) * (∫⁻ ω, (∫⁻ s, ENNReal.ofReal (‖v (s, ω)‖ ^ 2) ∂timeMeasure h) ^ p ∂μ)

theorem standardTerminalBDGPower_eight {Ω C E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup C] [NormedSpace ℝ C] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} {h : ℝ≥0}
    (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ h) (B : ℝ≥0) :
    StandardTerminalBDGPower 8 I B ↔ StandardTerminalBDG16 I B := Iff.rfl

namespace StandardTerminalBDGPower
variable {Ω C E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {h : ℝ≥0}

theorem moment_of_bracket_bound {p : ℕ}
    (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ h) {B : ℝ≥0}
    (hBDG : StandardTerminalBDGPower p I B) (v : Process (E := C) 𝓕 μ h)
    {K : ℝ} (hK : 0 ≤ K)
    (hbr : ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal (‖v (s, ω)‖ ^ 2) ∂timeMeasure h) ≤ ENNReal.ofReal K) :
    (∫⁻ ω, ENNReal.ofReal (‖I.integral v ω‖ ^ (2 * p)) ∂μ) ≤ ENNReal.ofReal ((B : ℝ) * K ^ p) := by
  have hp : (∫⁻ ω, (∫⁻ s, ENNReal.ofReal (‖v (s, ω)‖ ^ 2) ∂timeMeasure h) ^ p ∂μ) ≤
      (ENNReal.ofReal K) ^ p := by
    have hh := lintegral_mono_ae (hbr.mono (fun _ hω => pow_le_pow_left₀ (by simp) hω p))
    simpa only [lintegral_const, measure_univ, mul_one] using hh
  calc
    _ ≤ (B : ℝ≥0∞) * (∫⁻ ω, (∫⁻ s, ENNReal.ofReal (‖v (s, ω)‖ ^ 2) ∂timeMeasure h) ^ p ∂μ) := hBDG v
    _ ≤ (B : ℝ≥0∞) * (ENNReal.ofReal K) ^ p := mul_le_mul_right hp _
    _ = _ := by
      rw [← ENNReal.ofReal_pow hK, show (B : ℝ≥0∞) = ENNReal.ofReal (B : ℝ) by simp]
      exact (ENNReal.ofReal_mul B.2).symm

end StandardTerminalBDGPower

namespace PredictableItoRotation
variable {Ω A C E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup A] [NormedSpace ℝ A] [MeasurableSpace A] [BorelSpace A]
variable [NormedAddCommGroup C] [NormedSpace ℝ C] [MeasurableSpace C] [BorelSpace C]
variable [SecondCountableTopology C] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ] (h : ℝ≥0)
variable (Φ : (ℝ≥0 × Ω) → A →ₗᵢ[ℝ] C)
variable (hΦ : @Measurable ((ℝ≥0 × Ω) × A) C
  (𝓕.predictable.prod ‹MeasurableSpace A›) ‹MeasurableSpace C› (fun p => Φ p.1 p.2))

theorem bdgPower (p : ℕ) (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ h)
    (B : ℝ≥0) (hBDG : StandardTerminalBDGPower p I B) :
    StandardTerminalBDGPower p (integral 𝓕 μ h Φ hΦ I) B := by
  intro v
  apply (hBDG (processIsometry 𝓕 μ h Φ hΦ v)).trans_eq
  congr 1
  apply lintegral_congr_ae
  filter_upwards [bracket_ae 𝓕 μ h Φ hΦ v] with ω hω
  rw [hω]

end PredictableItoRotation
end SHE
