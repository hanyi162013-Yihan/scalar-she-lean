module

public import SHE.StandardTerminalBDGPower
public import Mathlib.MeasureTheory.Integral.MeanInequalities

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.FractionalMoment
open MeasureTheory
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Lyapunov's inequality in a form that also covers zero moments and
infinite intermediate quantities without additional integrability inputs. -/
theorem lintegral_fraction {F : Ω → ℝ≥0∞} (hF : AEMeasurable F μ)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    (∫⁻ ω, F ω ^ β ∂μ) ≤ (∫⁻ ω, F ω ∂μ) ^ β := by
  have hh := ENNReal.lintegral_mul_norm_pow_le hF
    (aemeasurable_const : AEMeasurable (fun _ : Ω => (1 : ℝ≥0∞)) μ)
    hβ (sub_nonneg.mpr hβ1) (by ring : β + (1 - β) = 1)
  simpa only [ENNReal.one_rpow, mul_one, lintegral_const, measure_univ] using hh

theorem moment_fraction {Y : Ω → ℝ} (hY : AEStronglyMeasurable Y μ)
    {q β C : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hC : 0 ≤ C)
    (hb : (∫⁻ ω, ENNReal.ofReal (‖Y ω‖ ^ q) ∂μ) ≤ ENNReal.ofReal C) :
    (∫⁻ ω, ENNReal.ofReal (‖Y ω‖ ^ (q * β)) ∂μ) ≤ ENNReal.ofReal (C ^ β) := by
  have hm : AEMeasurable (fun ω => ENNReal.ofReal (‖Y ω‖ ^ q)) μ :=
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable (hY.norm.aemeasurable.pow_const q)
  have he (ω : Ω) : ENNReal.ofReal (‖Y ω‖ ^ (q * β)) =
      ENNReal.ofReal (‖Y ω‖ ^ q) ^ β := by
    rw [Real.rpow_mul (norm_nonneg _), ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hβ]
  simp_rw [he]
  exact (lintegral_fraction hm hβ hβ1).trans
    ((ENNReal.rpow_le_rpow hb hβ).trans_eq (ENNReal.ofReal_rpow_of_nonneg hC hβ))

end SHE.FractionalMoment
