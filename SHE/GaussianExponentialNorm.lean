module

public import SHE.GaussianAudit

@[expose] public section
set_option autoImplicit false
noncomputable section

/-! Integrable polynomial-exponential envelopes for actual Gaussian laws.
These provide domination for rough-test differentiation on the full
physical covariance range, including singular Gaussian laws. -/
namespace SHE.GaussianExponentialNorm
open MeasureTheory ProbabilityTheory Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

theorem integrable_exp_norm (μ : Measure E) [IsGaussian μ] (a : ℝ) :
    Integrable (fun x : E => exp (a * ‖x‖)) μ := by
  obtain ⟨c, hc, hi⟩ := IsGaussian.exists_integrable_exp_sq μ
  apply (hi.const_mul (exp (a ^ 2 / (4 * c)))).mono'
    (by fun_prop)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), ← exp_add]
  apply exp_le_exp.mpr
  have hs := sq_nonneg (2 * c * ‖x‖ - a)
  have hcc : 0 < 4 * c := by positivity
  have hd : a ^ 2 / (4 * c) * (4 * c) = a ^ 2 := div_mul_cancel₀ _ hcc.ne'
  nlinarith

theorem integrable_pow_norm_mul_exp (μ : Measure E) [IsGaussian μ] (a : ℝ) (k : ℕ) :
    Integrable (fun x : E => ‖x‖ ^ k * exp (a * ‖x‖)) μ := by
  have hi := integrable_pow_abs_mul_exp_add_of_integrable_exp_mul
    (μ := μ) (X := fun x : E => ‖x‖) (v := a) (t := 1)
    (integrable_exp_norm μ (a + 1)) (integrable_exp_norm μ (a - 1))
    (show (0 : ℝ) ≤ 0 by rfl) (by norm_num : (0 : ℝ) < |1|) k
  simpa only [abs_norm, zero_mul, add_zero] using hi

theorem integrable_affine_norm_mul_exp (μ : Measure E) [IsGaussian μ] (a b : ℝ) :
    Integrable (fun x : E => (‖x‖ + b) * exp (a * ‖x‖)) μ := by
  convert! (integrable_pow_norm_mul_exp μ a 1).add ((integrable_exp_norm μ a).const_mul b) using 1
  funext x
  simp only [pow_one, Pi.add_apply]
  ring

end SHE.GaussianExponentialNorm
