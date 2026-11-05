module

public import SHE.GaussianProfileMean
public import SHE.SmoothCylinderAlgebra
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000
namespace SHE.ScalarGaussianSemigroup
open Set MeasureTheory ProbabilityTheory Filter Topology GaussianAudit GaussianSmooth SmoothCylinders
open scoped NNReal ENNReal

abbrev heat := GaussianAudit.gaussianConvolution

theorem heat_bound (v : ℝ≥0) {a : ℝ→ℝ} {B : ℝ} (hB : ∀ x,|a x|≤B) (x : ℝ) :
    |heat v a x|≤B := by
  simpa only [heat,gaussianConvolution,GaussianSmooth.average,Real.norm_eq_abs] using GaussianSmooth.average_norm_bound (gaussianReal 0 v)
    (fun z=>show ‖a z‖≤B by simpa only [Real.norm_eq_abs] using hB z) x

theorem heat_boundedSmooth (v : ℝ≥0) {a : ℝ→ℝ} (ha : BoundedSmooth a) :
    BoundedSmooth (heat v a) := ha.average (gaussianReal 0 v)

theorem deriv_boundedSmooth {a : ℝ→ℝ} (ha : BoundedSmooth a) : BoundedSmooth (deriv a) := by
  exact ha.fderiv.comp_left (ContinuousLinearMap.apply ℝ ℝ (1:ℝ))

theorem iteratedDeriv_boundedSmooth {a : ℝ→ℝ} (ha : BoundedSmooth a) (n : ℕ) :
    BoundedSmooth (iteratedDeriv n a) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using ha
  | succ n ih => rw [iteratedDeriv_succ]; exact deriv_boundedSmooth ih

/-- Exact scalar Gaussian semigroup on actual bounded Borel tests. -/
theorem heat_heat (v w : ℝ≥0) {a : ℝ→ℝ} (ha : Measurable a) {B : ℝ}
    (hB : ∀ x,|a x|≤B) : heat v (heat w a)=heat (v+w) a := by
  funext x
  have hi : Integrable (fun y : ℝ=>a (x+y)) ((gaussianReal 0 v)∗(gaussianReal 0 w)) := by
    exact (integrable_const B).mono' (ha.comp (measurable_const.add measurable_id)).aestronglyMeasurable
      (ae_of_all _ (fun y=>by simpa only [Real.norm_eq_abs] using hB (x+y)))
  have hh:=integral_conv hi
  rw [gaussianReal_conv_gaussianReal,zero_add] at hh
  simpa only [heat,gaussianConvolution,add_assoc] using hh.symm

theorem deriv_heat (v : ℝ≥0) {a : ℝ→ℝ} (ha : BoundedSmooth a) :
    deriv (heat v a)=heat v (deriv a) := by
  obtain ⟨B,hB⟩:=ha.norm_bound
  obtain ⟨L,hL⟩:=ha.fderiv.norm_bound
  funext x
  have hh:=GaussianSmooth.fderiv_average (gaussianReal 0 v) (ha.smooth.of_le (by simp)) hB hL
  change (fderiv ℝ (GaussianSmooth.average (gaussianReal 0 v) a) x) 1=_
  rw [hh]
  have hi:=GaussianSmooth.integrable_translate (gaussianReal 0 v)
    ha.fderiv.smooth.continuous hL x
  rw [ContinuousLinearMap.integral_apply hi]
  rfl

/-- Every finite actual derivative commutes with the scalar Gaussian
semigroup; bounded smoothness is used only for honest differentiation. -/
theorem iteratedDeriv_heat (v : ℝ≥0) {a : ℝ→ℝ} (ha : BoundedSmooth a) (n : ℕ) :
    iteratedDeriv n (heat v a)=heat v (iteratedDeriv n a) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n ih => rw [iteratedDeriv_succ,ih,deriv_heat v (iteratedDeriv_boundedSmooth ha n),iteratedDeriv_succ]

/-- Uniform approximation by actual Gaussian heat regularization, with
one genuine finite Gaussian moment and no coefficient derivative. -/
theorem heat_error (v : ℝ≥0) {a : ℝ→ℝ} (ha : Measurable a) {B H β : ℝ}
    (hB : ∀ x,|a x|≤B) (hβ : 0≤β)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (x : ℝ) :
    |heat v a x-a x|≤H*gaussianAbsMoment β*(v:ℝ)^(β/2) := by
  have hi : Integrable (fun z=>a (x+z)) (gaussianReal 0 v) :=
    (integrable_const B).mono' (ha.comp (measurable_const.add measurable_id)).aestronglyMeasurable
      (ae_of_all _ (fun z=>by simpa only [Real.norm_eq_abs] using hB (x+z)))
  have he : heat v a x-a x=∫ z,a (x+z)-a x ∂gaussianReal 0 v := by
    rw [integral_sub hi (integrable_const (a x)),integral_const]
    simp only [probReal_univ,one_smul]
    rfl
  rw [he,←Real.norm_eq_abs]
  calc
    _≤∫ z,‖a (x+z)-a x‖ ∂gaussianReal 0 v:=norm_integral_le_integral_norm _
    _≤∫ z,H*|z|^β ∂gaussianReal 0 v:=by
      apply integral_mono_ae (hi.sub (integrable_const (a x))).norm
        ((integrable_gaussian_abs_rpow v β hβ).const_mul H)
      exact ae_of_all _ (fun z=>by simpa only [Pi.sub_apply,Real.norm_eq_abs,add_sub_cancel_left] using hh (x+z) x)
    _=H*gaussianAbsMoment β*(v:ℝ)^(β/2):=by
      rw [integral_const_mul,gaussian_abs_rpow_moment v β hβ]
      ring

end SHE.ScalarGaussianSemigroup
