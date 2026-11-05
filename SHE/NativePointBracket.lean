module

public import SHE.NativeObservationEndpoint
public import SHE.TimeCausalPowers
public import SHE.ProfileVariance

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NativePointBracket
open MeasureTheory Set StoppedFourier FiniteHaar PredictableL2
open NativeObservationEndpoint
open scoped NNReal ENNReal
local instance nativePointBracket_periodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The actual physical endpoint row has a deterministic pathwise
quadratic-variation bound. Its coefficient may be arbitrary predictable
and random in the fixed elliptic interval. -/
theorem bracket_bound {Ω : Type*} [MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {h : ℝ≥0} (hh : (h : ℝ) ≤ 1) {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    (x : HeatCircle) :
    ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal
      (‖process 𝓕 μ h hell hM f hf le_rfl x (s, ω)‖ ^ 2) ∂timeMeasure h) ≤
        ENNReal.ofReal (ProfileVariance.upperConstant * M * (h : ℝ) ^ (1 / 2 : ℝ)) := by
  have he := process_ae 𝓕 μ h hell hM f hf (T := (h : ℝ)) le_rfl x
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure h)).quasiMeasurePreserving.ae he
  have hae := Measure.ae_ae_of_ae_prod hs
  filter_upwards [hae] with ω hω
  calc
    _ ≤ ∫⁻ s, ENNReal.ofReal (M * (1 + heatConstant)) *
        ENNReal.ofReal (((h : ℝ) - (s : ℝ)) ^ (-(1 / 2 : ℝ))) ∂timeMeasure h := by
      apply lintegral_mono_ae
      filter_upwards [hω, timeMeasure_ae_mem h] with s hrow hsh
      simp only [Prod.swap] at hrow
      change process 𝓕 μ h hell hM f hf le_rfl x (s, ω) = _ at hrow
      rw [hrow, ← ENNReal.ofReal_mul (mul_nonneg hM (by linarith [heatConstant_pos]))]
      apply ENNReal.ofReal_le_ofReal
      unfold fullIntegrand
      split_ifs with hlt
      · have hb := NativeObservationProcess.row_norm_sq_bound hell (f (s, ω)) hlt le_rfl x
        have hage : (h : ℝ) - (s : ℝ) ≤ 1 := by linarith [s.2]
        have hp := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
          (sub_pos.mpr hlt) hage (by norm_num : -(1 / 2 : ℝ) ≤ 0)
        have hmul := mul_le_mul_of_nonneg_left hp hM
        nlinarith
      · simp only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
        exact mul_nonneg (mul_nonneg hM (by linarith [heatConstant_pos]))
          (Real.rpow_nonneg (sub_nonneg.mpr (by exact_mod_cast hsh.2)) _)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        causal_rpow_mass (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))]
      norm_num only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num]
      rw [← ENNReal.ofReal_mul (mul_nonneg hM (by linarith [heatConstant_pos]))]
      congr 1
      unfold ProfileVariance.upperConstant
      ring

end SHE.NativePointBracket
