module

public import SHE.GaussianAudit
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section
set_option autoImplicit false

noncomputable section
namespace SHE.GaussianProfileMean
open MeasureTheory ProbabilityTheory SHE.GaussianAudit
open scoped NNReal ENNReal

/-- The genuine mean derivative of a Gaussian smoothing of a bounded Hölder
test gains the fractional power of its variance. The constant is an actual
finite standard Gaussian moment. -/
theorem gaussian_mean_derivative_holder_bound (v : ℝ≥0) (hv : v ≠ 0)
    (a : ℝ → ℝ) (ha : Measurable a) (M : ℝ) (hM : ∀ x, |a x| ≤ M)
    {β H : ℝ} (hβ : 0 ≤ β) (_hH : 0 ≤ H)
    (hholder : ∀ x y, |a x - a y| ≤ H * |x - y| ^ β) (m : ℝ) :
    |deriv (gaussianConvolution v a) m| ≤
      H * gaussianAbsMoment (β + 1) * (v : ℝ) ^ ((β - 1) / 2) := by
  have hvp : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hmeas : Measurable (fun z => a (m + z)) := by fun_prop
  have hi : Integrable (fun z => a (m + z) * firstScore v z) (gaussianReal 0 v) :=
    (integrable_firstScore v).bdd_mul hmeas.aestronglyMeasurable
      (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hM (m + z)))
  have hc := (integrable_firstScore v).const_mul (a m)
  have hic : Integrable (fun z => (a (m + z) - a m) * firstScore v z) (gaussianReal 0 v) := by
    convert! hi.sub hc using 1
    funext z
    dsimp only [Pi.sub_apply]
    ring
  have hcenter : (∫ z, a (m + z) * firstScore v z ∂gaussianReal 0 v) =
      ∫ z, (a (m + z) - a m) * firstScore v z ∂gaussianReal 0 v := by
    simp_rw [sub_mul]
    rw [integral_sub hi hc, integral_const_mul, integral_firstScore]
    simp
  have hip : Integrable (fun z : ℝ => H * (|z| ^ (β + 1) / (v : ℝ))) (gaussianReal 0 v) :=
    ((integrable_gaussian_abs_rpow v (β + 1) (by linarith)).div_const (v : ℝ)).const_mul H
  have hbound : ∀ z : ℝ, ‖(a (m + z) - a m) * firstScore v z‖ ≤
      H * (|z| ^ (β + 1) / (v : ℝ)) := by
    intro z
    have hh := hholder (m + z) m
    rw [add_sub_cancel_left] at hh
    have hp : |z| ^ (β + 1) = |z| ^ β * |z| :=
      Real.rpow_add_one' (abs_nonneg z) (by linarith)
    rw [Real.norm_eq_abs, abs_mul, firstScore, abs_div, abs_of_pos hvp, hp]
    have he := mul_le_mul_of_nonneg_right hh (div_nonneg (abs_nonneg z) hvp.le)
    convert! he using 1
    ring
  rw [(hasDerivAt_gaussianConvolution v hv a ha M hM m).deriv, hcenter]
  calc
    _ ≤ ∫ z, ‖(a (m + z) - a m) * firstScore v z‖ ∂gaussianReal 0 v :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z : ℝ, H * (|z| ^ (β + 1) / (v : ℝ)) ∂gaussianReal 0 v :=
      integral_mono_ae hic.norm hip (ae_of_all _ hbound)
    _ = H * gaussianAbsMoment (β + 1) * (v : ℝ) ^ ((β - 1) / 2) := by
      rw [integral_const_mul, integral_div, gaussian_abs_rpow_moment v (β + 1) (by linarith)]
      have hp : (v : ℝ) ^ ((β + 1) / 2) / (v : ℝ) = (v : ℝ) ^ ((β - 1) / 2) := by
        rw [← Real.rpow_sub_one hvp.ne']
        congr 1
        ring
      calc
        H * ((v : ℝ) ^ ((β + 1) / 2) * gaussianAbsMoment (β + 1) / (v : ℝ)) =
            H * gaussianAbsMoment (β + 1) * ((v : ℝ) ^ ((β + 1) / 2) / (v : ℝ)) := by ring
        _ = _ := by rw [hp]

/-- At fixed positive variance, the actual rough Gaussian average is Lipschitz
in its physical mean, with the same Hölder variance gain. -/
theorem gaussian_mean_lipschitz_holder_bound (v : ℝ≥0) (hv : v ≠ 0)
    (a : ℝ → ℝ) (ha : Measurable a) (M : ℝ) (hM : ∀ x, |a x| ≤ M)
    {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (hholder : ∀ x y, |a x - a y| ≤ H * |x - y| ^ β) (x y : ℝ) :
    |gaussianConvolution v a y - gaussianConvolution v a x| ≤
      (H * gaussianAbsMoment (β + 1) * (v : ℝ) ^ ((β - 1) / 2)) * |y - x| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := gaussianConvolution v a) (s := Set.univ)
    (fun m _ => (hasDerivAt_gaussianConvolution v hv a ha M hM m).differentiableAt)
    (fun m _ => by simpa only [Real.norm_eq_abs] using
      gaussian_mean_derivative_holder_bound v hv a ha M hM hβ hH hholder m)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ x) (Set.mem_univ y)
  simpa only [Real.norm_eq_abs] using h

/-- The physical mean Lipschitz constant is uniform over every variance above
a positive lower bound. This is the form used with elliptic heat variances. -/
theorem gaussian_mean_lipschitz_variance_lower_bound (v : ℝ≥0)
    (a : ℝ → ℝ) (ha : Measurable a) (M : ℝ) (hM : ∀ x, |a x| ≤ M)
    {β H lo : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hH : 0 ≤ H)
    (hlo : 0 < lo) (hv : lo ≤ (v : ℝ))
    (hholder : ∀ x y, |a x - a y| ≤ H * |x - y| ^ β) (x y : ℝ) :
    |gaussianConvolution v a y - gaussianConvolution v a x| ≤
      (H * gaussianAbsMoment (β + 1) * lo ^ ((β - 1) / 2)) * |y - x| := by
  have hv0 : v ≠ 0 := by exact_mod_cast (hlo.trans_le hv).ne'
  have he := Real.rpow_le_rpow_of_nonpos hlo hv (show (β - 1) / 2 ≤ 0 by linarith)
  have hcoef : 0 ≤ H * gaussianAbsMoment (β + 1) :=
    mul_nonneg hH (gaussianAbsMoment_nonneg _)
  exact (gaussian_mean_lipschitz_holder_bound v hv0 a ha M hM hβ hH hholder x y).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hcoef) (abs_nonneg _))

/-- An elliptic one-dimensional heat variance of order `sqrt r` gives the
physical quarter-power Hölder mean gain. -/
theorem gaussian_mean_lipschitz_heat_variance_bound (v : ℝ≥0)
    (a : ℝ → ℝ) (ha : Measurable a) (M : ℝ) (hM : ∀ x, |a x| ≤ M)
    {β H c r : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hH : 0 ≤ H)
    (hc : 0 < c) (hr : 0 < r) (hv : c * r ^ (1 / 2 : ℝ) ≤ (v : ℝ))
    (hholder : ∀ x y, |a x - a y| ≤ H * |x - y| ^ β) (x y : ℝ) :
    |gaussianConvolution v a y - gaussianConvolution v a x| ≤
      (H * gaussianAbsMoment (β + 1) * c ^ ((β - 1) / 2) * r ^ ((β - 1) / 4)) * |y - x| := by
  have hp : (c * r ^ (1 / 2 : ℝ)) ^ ((β - 1) / 2) =
      c ^ ((β - 1) / 2) * r ^ ((β - 1) / 4) := by
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg hr.le _), ← Real.rpow_mul hr.le]
    congr 2
    ring
  have he := gaussian_mean_lipschitz_variance_lower_bound v a ha M hM hβ hβ1 hH
    (mul_pos hc (Real.rpow_pos_of_pos hr _)) hv hholder x y
  rw [hp] at he
  convert! he using 1
  ring

end SHE.GaussianProfileMean
