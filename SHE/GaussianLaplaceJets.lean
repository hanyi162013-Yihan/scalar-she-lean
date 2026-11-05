module

public import SHE.GaussianLaplaceSmooth
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.GaussianLaplaceSmooth
open MeasureTheory ProbabilityTheory Real
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Actual derivatives at the origin are bounded by the matching Gaussian
norm moments. This applies also to operator-valued rough weights. -/
theorem norm_iterated_zero (k : ℕ) (μ : Measure E) [IsGaussian μ] {T : E → G}
    (hT : StronglyMeasurable T) {C b : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ y, ‖T y‖ ≤ C * exp (b * ‖y‖)) :
    ‖iteratedFDeriv ℝ k (transform μ T) 0‖ ≤ ∫ y, ‖y‖ ^ k * ‖T y‖ ∂μ := by
  induction k generalizing G b with
  | zero =>
      rw [norm_iteratedFDeriv_zero]
      simpa only [transform, inner_zero_left, exp_zero, one_smul, pow_zero, one_mul] using
        norm_integral_le_integral_norm (μ := μ) T
  | succ k ih =>
      rw [← norm_iteratedFDeriv_fderiv]
      have he : fderiv ℝ (transform μ T) = transform μ (step T) :=
        funext (fun a => (hasFDerivAt_transform μ hT hC hbound a).fderiv)
      rw [he]
      have hi := ih (stronglyMeasurable_step hT) (step_growth hC hbound)
      convert! hi using 1
      apply integral_congr_ae
      apply ae_of_all
      intro y
      simp only [step, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, pow_succ]
      ring

theorem norm_iterated_zero_bounded (k : ℕ) (μ : Measure E) [IsGaussian μ]
    {T : E → G} (hT : StronglyMeasurable T) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ y, ‖T y‖ ≤ M) :
    ‖iteratedFDeriv ℝ k (transform μ T) 0‖ ≤ M * ∫ y, ‖y‖ ^ k ∂μ := by
  have hb : ∀ y, ‖T y‖ ≤ M * exp (0 * ‖y‖) := by simpa using hbound
  have hi := norm_iterated_zero k μ hT hM hb
  apply hi.trans
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg
    (ae_of_all _ (fun y => mul_nonneg (pow_nonneg (norm_nonneg y) _) (norm_nonneg _)))
    ((GaussianExponentialNorm.integrable_pow_norm_mul_exp μ 0 k).const_mul M |>.congr
      (ae_of_all _ (fun y => by simp)))
  exact ae_of_all _ (fun y => by
    simpa only [mul_comm M] using mul_le_mul_of_nonneg_left (hbound y) (pow_nonneg (norm_nonneg y) _))

end SHE.GaussianLaplaceSmooth
