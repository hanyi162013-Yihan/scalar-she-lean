module

public import SHE.StandardTerminalBDGPower

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace SHE.PredictableBracketDifference
open MeasureTheory PredictableL2
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω] [NormedAddCommGroup C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ] (h : ℝ≥0)

theorem bracket_sub_le (v w : Process (E := C) 𝓕 μ h) :
    ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal (‖(v - w : Process (E := C) 𝓕 μ h) (s, ω)‖ ^ 2) ∂timeMeasure h) ≤
      2 * (∫⁻ s, ENNReal.ofReal (‖v (s, ω)‖ ^ 2) ∂timeMeasure h) +
      2 * (∫⁻ s, ENNReal.ofReal (‖w (s, ω)‖ ^ 2) ∂timeMeasure h) := by
  have he : ∀ᵐ p ∂energyMeasure μ h, (v - w : Process (E := C) 𝓕 μ h) p = v p - w p :=
    ae_eq_of_ae_eq_trim (Lp.coeFn_sub v w)
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure h)).quasiMeasurePreserving.ae he
  have hvm : Measurable (fun p => ENNReal.ofReal (‖v p‖ ^ 2)) :=
    ENNReal.continuous_ofReal.measurable.comp
      (((Lp.stronglyMeasurable v).mono (predictable_le_product 𝓕)).norm.measurable.pow_const 2)
  have hwm : Measurable (fun p => ENNReal.ofReal (‖w p‖ ^ 2)) :=
    ENNReal.continuous_ofReal.measurable.comp
      (((Lp.stronglyMeasurable w).mono (predictable_le_product 𝓕)).norm.measurable.pow_const 2)
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  calc
    _ ≤ ∫⁻ s, 2 * ENNReal.ofReal (‖v (s, ω)‖ ^ 2) +
        2 * ENNReal.ofReal (‖w (s, ω)‖ ^ 2) ∂timeMeasure h := by
      apply lintegral_mono_ae
      filter_upwards [hω] with s hs
      simp only [Prod.swap] at hs
      rw [hs]
      have hb : ‖v (s, ω) - w (s, ω)‖ ^ 2 ≤ 2 * ‖v (s, ω)‖ ^ 2 + 2 * ‖w (s, ω)‖ ^ 2 := by
        have ht := norm_sub_le (v (s, ω)) (w (s, ω))
        have hp := sq_le_sq₀ (norm_nonneg (v (s, ω) - w (s, ω)))
          (add_nonneg (norm_nonneg (v (s, ω))) (norm_nonneg (w (s, ω))))
        have hh := hp.mpr ht
        nlinarith [sq_nonneg (‖v (s, ω)‖ - ‖w (s, ω)‖)]
      have hh := ENNReal.ofReal_le_ofReal hb
      simpa only [ENNReal.ofReal_add (by positivity : 0 ≤ 2 * ‖v (s, ω)‖ ^ 2)
          (by positivity : 0 ≤ 2 * ‖w (s, ω)‖ ^ 2),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] using hh
    _ = _ := by
      have hvω : Measurable (fun s : ℝ≥0 => (2 : ℝ≥0∞) * ENNReal.ofReal (‖v (s, ω)‖ ^ 2)) :=
        (measurable_const (a := (2 : ℝ≥0∞))).mul
          (hvm.comp (show Measurable (fun s : ℝ≥0 => (s, ω)) from measurable_id.prodMk measurable_const))
      have hsplit := lintegral_add_left (μ := timeMeasure h) hvω
        (fun s : ℝ≥0 => (2 : ℝ≥0∞) * ENNReal.ofReal (‖w (s, ω)‖ ^ 2))
      rw [hsplit,
        lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
        lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]

theorem bracket_sub_bound (v w : Process (E := C) 𝓕 μ h) {K : ℝ} (hK : 0 ≤ K)
    (hv : ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal (‖v (s, ω)‖ ^ 2) ∂timeMeasure h) ≤ ENNReal.ofReal K)
    (hw : ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal (‖w (s, ω)‖ ^ 2) ∂timeMeasure h) ≤ ENNReal.ofReal K) :
    ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal (‖(v - w : Process (E := C) 𝓕 μ h) (s, ω)‖ ^ 2) ∂timeMeasure h) ≤
      ENNReal.ofReal (4 * K) := by
  filter_upwards [bracket_sub_le 𝓕 μ h v w, hv, hw] with ω hω hv hw
  apply hω.trans
  calc
    _ ≤ 2 * ENNReal.ofReal K + 2 * ENNReal.ofReal K :=
      add_le_add (mul_le_mul_right hv _) (mul_le_mul_right hw _)
    _ = _ := by
      rw [show (4 : ℝ) * K = 2 * K + 2 * K by ring,
        ENNReal.ofReal_add (mul_nonneg (by norm_num) hK) (mul_nonneg (by norm_num) hK)]
      simp only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]

end SHE.PredictableBracketDifference
