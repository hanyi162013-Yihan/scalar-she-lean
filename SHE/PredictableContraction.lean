module

public import SHE.StandardTerminalBDGPower

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section

namespace SHE.PredictableContraction
open MeasureTheory PredictableL2
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω] [NormedAddCommGroup C] [NormedSpace ℝ C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (h : ℝ≥0)
variable (a : ℝ≥0 × Ω → ℝ) (ha : StronglyMeasurable[𝓕.predictable] a)
variable (hbound : ∀ p, |a p| ≤ 1)

include ha hbound in
theorem weighted_memLp (v : Process (E := C) 𝓕 μ h) :
    @MemLp _ _ 𝓕.predictable _ _ (fun p => a p • v p) 2
      ((energyMeasure μ h).trim (predictable_le_product 𝓕)) := by
  apply (Lp.memLp v).of_le_mul (c := (1 : ℝ))
    ((ha.smul (Lp.stronglyMeasurable v)).aestronglyMeasurable)
  filter_upwards with p
  change ‖a p • v p‖ ≤ 1 * ‖v p‖
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hbound p) (norm_nonneg _)

def weighted (v : Process (E := C) 𝓕 μ h) : Process (E := C) 𝓕 μ h :=
  (weighted_memLp 𝓕 μ h a ha hbound v).toLp (fun p => a p • v p)

theorem weighted_ae (v : Process (E := C) 𝓕 μ h) :
    weighted 𝓕 μ h a ha hbound v =ᵐ[energyMeasure μ h] (fun p => a p • v p) :=
  ae_eq_of_ae_eq_trim (weighted_memLp 𝓕 μ h a ha hbound v).coeFn_toLp

theorem bracket_le [SFinite μ] (v : Process (E := C) 𝓕 μ h) :
    ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal
      (‖weighted 𝓕 μ h a ha hbound v (s, ω)‖ ^ 2) ∂timeMeasure h) ≤
      (∫⁻ s, ENNReal.ofReal (‖v (s, ω)‖ ^ 2) ∂timeMeasure h) := by
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure h)).quasiMeasurePreserving.ae
    (weighted_ae 𝓕 μ h a ha hbound v)
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  apply lintegral_mono_ae
  filter_upwards [hω] with s hs
  simp only [Prod.swap] at hs
  rw [hs]
  apply ENNReal.ofReal_le_ofReal
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  rw [norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (hbound (s, ω)) (norm_nonneg _)).trans_eq (one_mul _)

end SHE.PredictableContraction
