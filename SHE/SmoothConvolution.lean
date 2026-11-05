module

public import SHE.SmoothCylinders
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Support

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace SHE.SmoothConvolution
open MeasureTheory ContinuousLinearMap
open scoped Convolution ContDiff
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def convolve (a : ℝ → ℝ) (k : ℝ → E) : ℝ → E :=
  a ⋆[lsmul ℝ ℝ,volume] k

omit [CompleteSpace E] in
theorem convolve_eq (a : ℝ → ℝ) (k : ℝ → E) (x : ℝ) :
    convolve a k x=∫ y,a (x-y) • k y := convolution_lsmul_swap

omit [CompleteSpace E] in
theorem compact_jet {k : ℝ → E} (hk : HasCompactSupport k) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n k) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hk
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

omit [CompleteSpace E] in
theorem smooth_jet {k : ℝ → E} (hk : ContDiff ℝ ∞ k) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n k) := by
  rw [iteratedDeriv_eq_iterate]
  exact hk.iterate_deriv n

omit [CompleteSpace E] in
theorem convolve_smooth {a : ℝ → ℝ} (ha : Continuous a) {k : ℝ → E}
    (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) : ContDiff ℝ ∞ (convolve a k) :=
  hc.contDiff_convolution_right (lsmul ℝ ℝ) ha.locallyIntegrable hk

omit [CompleteSpace E] in
theorem iteratedDeriv_convolve {a : ℝ → ℝ} (ha : Continuous a) {k : ℝ → E}
    (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) (n : ℕ) :
    iteratedDeriv n (convolve a k)=convolve a (iteratedDeriv n k) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    have haI : LocallyIntegrable a (volume : Measure ℝ) := ha.locallyIntegrable
    have hh : HasDerivAt (convolve a (iteratedDeriv n k))
        (convolve a (deriv (iteratedDeriv n k)) x) x :=
      HasCompactSupport.hasDerivAt_convolution_right (lsmul ℝ ℝ) haI
        (compact_jet hc n) ((smooth_jet hk n).of_le (by simp)) x
    simpa only [convolve,iteratedDeriv_succ] using hh.deriv

omit [CompleteSpace E] in
theorem convolve_norm_bound {a : ℝ → ℝ} (ha : Continuous a) {B : ℝ}
    (hB : ∀ x,|a x| ≤ B) {k : ℝ → E} (hk : Continuous k) (hI : Integrable k)
    (x : ℝ) : ‖convolve a k x‖ ≤ B*(∫ y,‖k y‖) := by
  have hi : Integrable (fun y => a (x-y) • k y) := by
    apply (hI.norm.const_mul B).mono' (by fun_prop)
    exact Filter.Eventually.of_forall (fun y => by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hB (x-y)) (norm_nonneg _))
  rw [convolve_eq]
  calc
    _ ≤ ∫ y,‖a (x-y) • k y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y,B*‖k y‖ := by
      apply integral_mono hi.norm (hI.norm.const_mul B)
      intro y
      change ‖a (x-y) • k y‖ ≤ B*‖k y‖
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hB (x-y)) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

/-- Bounded continuous rough coefficients convolved with an actual compact
smooth kernel have genuine globally bounded derivatives of every order. -/
theorem convolve_boundedSmooth {a : ℝ → ℝ} (ha : Continuous a) {B : ℝ}
    (hB : ∀ x,|a x| ≤ B) {k : ℝ → E} (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) :
    SmoothCylinders.BoundedSmooth (convolve a k) := by
  refine ⟨convolve_smooth ha hk hc,fun n => ?_⟩
  refine ⟨B*(∫ y,‖iteratedDeriv n k y‖),fun x => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_convolve ha hk hc n]
  exact convolve_norm_bound ha hB (smooth_jet hk n).continuous
    ((smooth_jet hk n).continuous.integrable_of_hasCompactSupport (compact_jet hc n)) x

end SHE.SmoothConvolution
