module

public import SHE.NativePointBracket

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.NativeHeatPointBracket
open MeasureTheory Set StoppedFourier FiniteHaar PredictableL2 NativeObservationEndpoint
open scoped NNReal ENNReal
local instance nativeHeatPointBracket_periodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Further deterministic heat smoothing of a point observation preserves
the native quarter-time noise scale. The original terminal target T and
physical stopping time h remain distinct. -/
theorem bracket_bound {Ω : Type*} [MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {h : ℝ≥0} (hh : (h : ℝ) ≤ 1) {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    {T : ℝ} (hT : (h : ℝ) ≤ T) (x : HeatCircle) :
    ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal
      (‖process 𝓕 μ h hell hM f hf hT x (s, ω)‖ ^ 2) ∂timeMeasure h) ≤
        ENNReal.ofReal (ProfileVariance.upperConstant * M * (h : ℝ) ^ (1 / 2 : ℝ)) := by
  have he := process_ae 𝓕 μ h hell hM f hf hT x
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure h)).quasiMeasurePreserving.ae he
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  calc
    _ ≤ ∫⁻ s, ENNReal.ofReal (M * (1 + heatConstant)) *
        ENNReal.ofReal (((h : ℝ) - (s : ℝ)) ^ (-(1 / 2 : ℝ))) ∂timeMeasure h := by
      apply lintegral_mono_ae
      filter_upwards [hω, timeMeasure_ae_mem h, (timeMeasure h).ae_ne h] with s hrow hsh hne
      simp only [Prod.swap] at hrow
      have hlt : (s : ℝ) < (h : ℝ) := by exact_mod_cast lt_of_le_of_ne hsh.2 hne
      have hst : (s : ℝ) < T := hlt.trans_le hT
      rw [hrow, fullIntegrand, if_pos hst,
        ← ENNReal.ofReal_mul (mul_nonneg hM (by linarith [heatConstant_pos]))]
      apply ENNReal.ofReal_le_ofReal
      have hbefore : (s : ℝ) + T - (h : ℝ) < T := by linarith
      have hafter : (s : ℝ) ≤ (s : ℝ) + T - (h : ℝ) := by linarith
      have hb := NativeObservationProcess.row_norm_sq_bound hell (f (s, ω)) hbefore hafter x
      rw [show T - ((s : ℝ) + T - (h : ℝ)) = (h : ℝ) - (s : ℝ) by ring] at hb
      have hage : (h : ℝ) - (s : ℝ) ≤ 1 := by linarith [s.2]
      have hp := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
        (sub_pos.mpr hlt) hage (by norm_num : -(1 / 2 : ℝ) ≤ 0)
      have hmul := mul_le_mul_of_nonneg_left hp hM
      nlinarith
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        causal_rpow_mass (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))]
      norm_num only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num]
      rw [← ENNReal.ofReal_mul (mul_nonneg hM (by linarith [heatConstant_pos]))]
      congr 1
      unfold ProfileVariance.upperConstant
      ring

end SHE.NativeHeatPointBracket
