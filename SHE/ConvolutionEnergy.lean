module

public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE
open MeasureTheory Set
open scoped ENNReal

/-- Tonelli and translation invariance give the actual finite-time
energy estimate for a stochastic convolution after its isometry has
been supplied. No stochastic or analytic estimate is assumed here. -/
theorem finite_time_convolution_energy_bound
    (K F : ℝ → ℝ≥0∞) (hK : Measurable K) (hF : Measurable F) (T : ℝ) :
    (∫⁻ t in Ioc (0:ℝ) T, ∫⁻ s in Ioc (0:ℝ) T, K (t-s) * F s) ≤
      (∫⁻ u : ℝ, K u) * ∫⁻ s in Ioc (0:ℝ) T, F s := by
  calc
    _ ≤ ∫⁻ t : ℝ, ∫⁻ s in Ioc (0:ℝ) T, K (t-s) * F s :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ∫⁻ s in Ioc (0:ℝ) T, ∫⁻ t : ℝ, K (t-s) * F s := by
      apply lintegral_lintegral_swap
      exact ((hK.comp (measurable_fst.sub measurable_snd)).mul (hF.comp measurable_snd)).aemeasurable
    _ = (∫⁻ u : ℝ, K u) * ∫⁻ s in Ioc (0:ℝ) T, F s := by
      have hin (s : ℝ) : (∫⁻ t : ℝ, K (t-s) * F s) = (∫⁻ u : ℝ, K u) * F s := by
        have hsmeas : Measurable (fun t : ℝ => K (t-s)) := hK.comp (measurable_id.sub_const s)
        rw [lintegral_mul_const (F s) hsmeas, lintegral_sub_right_eq_self]
      simp only [hin]
      exact lintegral_const_mul _ hF

/-- A causal kernel can be integrated over the true ordered simplex;
the upper limit of its input integral is the current time. -/
theorem causal_convolution_energy_bound
    (K F : ℝ → ℝ≥0∞) (hK : Measurable K) (hF : Measurable F) (T : ℝ) :
    (∫⁻ t in Ioc (0:ℝ) T, ∫⁻ s in Ioc (0:ℝ) t, K (t-s) * F s) ≤
      (∫⁻ u : ℝ, K u) * ∫⁻ s in Ioc (0:ℝ) T, F s := by
  apply le_trans _ (finite_time_convolution_energy_bound K F hK hF T)
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact lintegral_mono_set (Ioc_subset_Ioc_right ht.2)

/-- Finiteness follows from finite kernel mass and finite input energy,
so the comparison cannot be an infinite-energy inequality. -/
theorem causal_convolution_energy_finite
    (K F : ℝ → ℝ≥0∞) (hK : Measurable K) (hF : Measurable F) (T : ℝ)
    (hKfin : (∫⁻ u : ℝ, K u) < ∞) (hFfin : (∫⁻ s in Ioc (0:ℝ) T, F s) < ∞) :
    (∫⁻ t in Ioc (0:ℝ) T, ∫⁻ s in Ioc (0:ℝ) t, K (t-s) * F s) < ∞ :=
  (causal_convolution_energy_bound K F hK hF T).trans_lt (ENNReal.mul_lt_top hKfin hFfin)

end SHE
