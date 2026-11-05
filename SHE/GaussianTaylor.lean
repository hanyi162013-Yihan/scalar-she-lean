module

public import SHE.GaussianSmooth

@[expose] public section
set_option autoImplicit false

/-! A uniform smooth-cylinder Taylor estimate for actual Gaussian increments. -/
noncomputable section
namespace SHE.GaussianTaylor
open Set MeasureTheory ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def hessian (F : E → ℝ) (z : E) : E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ F) z

theorem bilinear_norm_le (H : E →L[ℝ] E →L[ℝ] ℝ) (x y : E) :
    ‖H x y‖ ≤ ‖H‖ * ‖x‖ * ‖y‖ :=
  ((H x).le_opNorm y).trans (mul_le_mul_of_nonneg_right (H.le_opNorm x) (norm_nonneg y))

/-- The actual bounded Hessian gives a uniform quadratic first-order
remainder, without a third derivative or a nondegenerate covariance. -/
theorem first_order_remainder {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {B : ℝ} (hB : 0 ≤ B) (hDD : ∀ z, ‖hessian F z‖ ≤ B) (z x : E) :
    ‖F (z + x) - F z - fderiv ℝ F z x‖ ≤ B * ‖x‖ ^ 2 := by
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
  have hF1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hgrad (v w : E) : ‖fderiv ℝ F w - fderiv ℝ F v‖ ≤ B * ‖w - v‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => hF1.differentiable (by norm_num) y) (fun y _ => hDD y)
      convex_univ (mem_univ v) (mem_univ w)
  let g : ℝ → ℝ := fun t => F (z + t • x) - F z - t * fderiv ℝ F z x
  have hg (t : ℝ) : HasDerivAt g ((fderiv ℝ F (z + t • x) - fderiv ℝ F z) x) t := by
    have hl : HasDerivAt (fun t : ℝ => z + t • x) x t := by
      simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const x).const_add z
    have hh := ((hF.differentiable (by norm_num) (z + t • x)).hasFDerivAt.comp_hasDerivAt t hl).sub_const (F z)
    convert hh.sub ((hasDerivAt_id t).mul_const (fderiv ℝ F z x)) using 1
    · rfl
    · simp only [sub_apply, one_mul]
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖(fderiv ℝ F (z + t • x) - fderiv ℝ F z) x‖ ≤ B * ‖x‖ ^ 2 := by
    calc
      _ ≤ ‖fderiv ℝ F (z + t • x) - fderiv ℝ F z‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (B * ‖(z + t • x) - z‖) * ‖x‖ := mul_le_mul_of_nonneg_right (hgrad z _) (norm_nonneg _)
      _ = t * (B * ‖x‖ ^ 2) := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        ring
      _ ≤ _ := mul_le_of_le_one_left (by positivity) ht.2
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hg t).hasDerivWithinAt) hb (convex_Icc (0 : ℝ) 1)
    (show (0 : ℝ) ∈ Icc 0 1 by norm_num) (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
  simpa only [g, zero_smul, add_zero, zero_mul, sub_self, sub_zero, one_smul, one_mul,
    norm_one, mul_one] using hh

/-- A loose cubic remainder is sufficient for covariance differentiation;
the bound is uniform in the base point and every collision configuration. -/
theorem second_order_remainder {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {B : ℝ} (hB : 0 ≤ B)
    (hH : ∀ z w, ‖hessian F w - hessian F z‖ ≤ B * ‖w - z‖) (z x : E) :
    ‖F (z + x) - F z - fderiv ℝ F z x - (1 / 2 : ℝ) * hessian F z x x‖ ≤ B * ‖x‖ ^ 3 := by
  let g : ℝ → ℝ := fun t => F (z + t • x) - F z - t * fderiv ℝ F z x -
    (t ^ 2 / 2) * hessian F z x x
  let k : ℝ → ℝ := fun t => fderiv ℝ F (z + t • x) x - fderiv ℝ F z x - t * hessian F z x x
  have hline (t : ℝ) : HasDerivAt (fun t : ℝ => z + t • x) x t := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const x).const_add z
  have hg (t : ℝ) : HasDerivAt g (k t) t := by
    have hf := (hF.differentiable (by norm_num) (z + t • x)).hasFDerivAt.comp_hasDerivAt t (hline t)
    convert (((hf.sub_const (F z)).sub ((hasDerivAt_id t).mul_const (fderiv ℝ F z x))).sub
      (((hasDerivAt_id t).pow 2).div_const 2 |>.mul_const (hessian F z x x))) using 1
    · rfl
    · dsimp [k]; ring
  have hk (t : ℝ) : HasDerivAt k ((hessian F (z + t • x) - hessian F z) x x) t := by
    have hF1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
    have hf0 := (hF1.differentiable (by norm_num) (z + t • x)).hasFDerivAt.comp_hasDerivAt t (hline t)
    have hf := (ContinuousLinearMap.apply ℝ ℝ x).hasFDerivAt.comp_hasDerivAt t hf0
    convert (hf.sub_const (fderiv ℝ F z x)).sub ((hasDerivAt_id t).mul_const (hessian F z x x)) using 1
    · simp only [Function.comp_def, ContinuousLinearMap.apply_apply]; rfl
    · simp only [hessian, ContinuousLinearMap.apply_apply, one_mul, sub_apply]
  let C : ℝ := B * ‖x‖ ^ 3
  have hC : 0 ≤ C := mul_nonneg hB (by positivity)
  have hkb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖(hessian F (z + t • x) - hessian F z) x x‖ ≤ C := by
    calc
      _ ≤ ‖hessian F (z + t • x) - hessian F z‖ * ‖x‖ * ‖x‖ := bilinear_norm_le _ _ _
      _ ≤ (B * ‖(z + t • x) - z‖) * ‖x‖ * ‖x‖ := by gcongr; exact hH z _
      _ = t * C := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        dsimp [C]
        ring
      _ ≤ C := mul_le_of_le_one_left hC ht.2
  have hknorm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖k t‖ ≤ C := by
    have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s _ => (hk s).hasDerivWithinAt) hkb (convex_Icc (0 : ℝ) 1)
      (show (0 : ℝ) ∈ Icc 0 1 by norm_num) ht
    have hk0 : k 0 = 0 := by simp [k]
    simp only [hk0, sub_zero, Real.norm_eq_abs, abs_of_nonneg ht.1] at hh
    exact hh.trans (mul_le_of_le_one_right hC ht.2)
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hg t).hasDerivWithinAt) hknorm (convex_Icc (0 : ℝ) 1)
    (show (0 : ℝ) ∈ Icc 0 1 by norm_num) (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
  simpa only [g, zero_smul, add_zero, zero_mul, zero_pow (by norm_num : 2 ≠ 0),
    zero_div, sub_self, sub_zero, one_smul, one_pow, one_div, sub_zero, one_mul,
    norm_one, mul_one, C] using hh

end SHE.GaussianTaylor
