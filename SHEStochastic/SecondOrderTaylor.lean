module

public import SHE.GaussianTaylor

/-! The two one-dimensional mean-value estimates below reuse the existing
GaussianTaylor.second_order_remainder proof, replacing the Lipschitz
Hessian bound by its oscillation along the actual line segment. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section

namespace SHEStochastic.SecondOrderTaylor
open Set SHE.GaussianTaylor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous Hessian needs only a segment oscillation estimate;
no third derivative or Lipschitz Hessian is required. -/
theorem remainder_of_oscillation {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (z x : E) (η : ℝ) (hη : 0 ≤ η)
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, ‖hessian F (z + t • x) - hessian F z‖ ≤ η) :
    ‖F (z + x) - F z - fderiv ℝ F z x - (1 / 2 : ℝ) * hessian F z x x‖ ≤ η * ‖x‖ ^ 2 := by
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
  let C : ℝ := η * ‖x‖ ^ 2
  have hC : 0 ≤ C := mul_nonneg hη (sq_nonneg _)
  have hkb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖(hessian F (z + t • x) - hessian F z) x x‖ ≤ C := by
    calc
      _ ≤ ‖hessian F (z + t • x) - hessian F z‖ * ‖x‖ * ‖x‖ := bilinear_norm_le _ _ _
      _ ≤ η * ‖x‖ * ‖x‖ := by gcongr; exact hH t ht
      _ = C := by dsimp [C]; ring
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


def remainder (F : E → ℝ) (x y : E) : ℝ :=
  F y - F x - fderiv ℝ F x (y - x) - (1 / 2 : ℝ) * hessian F x (y - x) (y - x)

theorem remainder_bound {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (x y : E) (η : ℝ) (hη : 0 ≤ η)
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, ‖hessian F (x + t • (y - x)) - hessian F x‖ ≤ η) :
    ‖remainder F x y‖ ≤ η * ‖y - x‖ ^ 2 := by
  simpa only [remainder, add_sub_cancel] using remainder_of_oscillation hF x (y - x) η hη hH

end SHEStochastic.SecondOrderTaylor
