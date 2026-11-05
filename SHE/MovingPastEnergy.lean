module

public import SHE.ConvolutionEnergy

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.MovingPastEnergy
open Set MeasureTheory
open scoped ENNReal

/-- Averaging the true current input over a moving old past uses only
translation invariance and Tonelli. Its global energy is counted once;
there is no independence or pointwise-in-time input bound. -/
theorem window_bound (K F : ℝ → ℝ≥0∞) (hK : Measurable K) (hF : Measurable F)
    (T h : ℝ) :
    (∫⁻ v in Ioc (0:ℝ) T,∫⁻ q in Ioc (0:ℝ) h,K q*F (v+q)) ≤
      (∫⁻ q in Ioc (0:ℝ) h,K q)*(∫⁻ r : ℝ,F r) := by
  calc
    _ = ∫⁻ q in Ioc (0:ℝ) h,∫⁻ v in Ioc (0:ℝ) T,K q*F (v+q) := by
      apply lintegral_lintegral_swap
      exact ((hK.comp measurable_snd).mul
        (hF.comp (measurable_fst.add measurable_snd))).aemeasurable
    _ ≤ ∫⁻ q in Ioc (0:ℝ) h,∫⁻ v : ℝ,K q*F (v+q) := by
      apply lintegral_mono
      intro q
      exact lintegral_mono' Measure.restrict_le_self le_rfl
    _ = _ := by
      have hin (q : ℝ) : (∫⁻ v : ℝ,K q*F (v+q))=K q*(∫⁻ r : ℝ,F r) := by
        have hmq : Measurable (fun v : ℝ => F (v+q)) := hF.comp (measurable_id.add_const q)
        rw [lintegral_const_mul _ hmq,lintegral_add_right_eq_self]
      simp only [hin]
      exact lintegral_mul_const _ hK

theorem window_finite (K F : ℝ → ℝ≥0∞) (hK : Measurable K) (hF : Measurable F)
    (T h : ℝ) (hKi : (∫⁻ q in Ioc (0:ℝ) h,K q) < ∞)
    (hFi : (∫⁻ r : ℝ,F r) < ∞) :
    (∫⁻ v in Ioc (0:ℝ) T,∫⁻ q in Ioc (0:ℝ) h,K q*F (v+q)) < ∞ :=
  (window_bound K F hK hF T h).trans_lt (ENNReal.mul_lt_top hKi hFi)

end SHE.MovingPastEnergy
