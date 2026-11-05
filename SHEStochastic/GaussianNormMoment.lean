module

public import SHEStochastic.MatrixSqrtReference
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Fernique

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.GaussianNormMoment
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
variable {d : Type*} [Fintype d] [DecidableEq d]

def moment (d : Type*) [Fintype d] (β : ℝ) : ℝ :=
  ∫ z : EuclideanSpace ℝ d, ‖z‖^β ∂stdGaussian (EuclideanSpace ℝ d)

theorem nonneg (β : ℝ) : 0 ≤ moment d β :=
  integral_nonneg (fun z => Real.rpow_nonneg (norm_nonneg z) _)

theorem integrable (μ : Measure (EuclideanSpace ℝ d)) [IsGaussian μ]
    {β : ℝ} (hβ : 0 ≤ β) : Integrable (fun z => ‖z‖^β) μ := by
  simpa only [id_eq, ENNReal.toReal_ofReal hβ] using
    (IsGaussian.memLp_id μ (ENNReal.ofReal β) ENNReal.ofReal_ne_top).integrable_norm_rpow'

/-- Every positive covariance obeys the Gaussian norm-moment scaling
bound, including singular covariance matrices. -/
theorem bound (A : Matrix d d ℝ) (hA : 0 ≤ A) {V β : ℝ}
    (hV : 0 ≤ V) (hAV : ‖A‖ ≤ V) (hβ : 0 ≤ β) :
    (∫ z : EuclideanSpace ℝ d, ‖z‖^β ∂multivariateGaussian 0 A) ≤ V^(β/2)*moment d β := by
  let S := Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (CFC.sqrt A)
  have hS : ‖S‖ ≤ Real.sqrt V := by
    change ‖CFC.sqrt A‖ ≤ Real.sqrt V
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg V)).mp
    rw [MatrixSqrtReference.sqrt_norm_sq A hA, Real.sq_sqrt hV]
    exact hAV
  have hp (z : EuclideanSpace ℝ d) : ‖S z‖^β ≤ V^(β/2)*‖z‖^β := by
    have hn := (S.le_opNorm z).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg z))
    have hh := Real.rpow_le_rpow (norm_nonneg (S z)) hn hβ
    rw [Real.mul_rpow (Real.sqrt_nonneg V) (norm_nonneg z),Real.sqrt_eq_rpow,
      ← Real.rpow_mul hV,show (1/2 : ℝ)*β=β/2 by ring] at hh
    exact hh
  have hi := (integrable (stdGaussian (EuclideanSpace ℝ d)) hβ).const_mul (V^(β/2))
  rw [multivariateGaussian, integral_map (by fun_prop) (by fun_prop)]
  simp only [zero_add]
  calc
    _ ≤ ∫ z : EuclideanSpace ℝ d, V^(β/2)*‖z‖^β ∂stdGaussian (EuclideanSpace ℝ d) := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun z => Real.rpow_nonneg (norm_nonneg (S z)) β) hi
      exact Filter.Eventually.of_forall hp
    _ = _ := by rw [integral_const_mul]; rfl

end SHEStochastic.GaussianNormMoment
