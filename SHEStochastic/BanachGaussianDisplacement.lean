module

public import SHEStochastic.GaussianNormMoment

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.BanachGaussianDisplacement
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
variable {d E : Type*} [Fintype d] [DecidableEq d]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The displacement estimate is Banach valued, so the same proof
applies to a full matrix covariance or any finite collection of tests. -/
theorem bound (F : EuclideanSpace ℝ d → E) (hF : StronglyMeasurable F)
    (M : ℝ) (hM : ∀ z, ‖F z‖ ≤ M) {K β V : ℝ}
    (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (hH : ∀ z w, ‖F z-F w‖ ≤ K*‖z-w‖^β)
    (A : Matrix d d ℝ) (hA : 0 ≤ A) (hV : 0 ≤ V) (hAV : ‖A‖ ≤ V)
    (m : EuclideanSpace ℝ d) :
    ‖(∫ z, F (m+z) ∂multivariateGaussian 0 A)-F m‖ ≤
      K*V^(β/2)*GaussianNormMoment.moment d β := by
  have hi : Integrable (fun z => F (m+z)) (multivariateGaussian 0 A) :=
    Integrable.of_bound (hF.comp_measurable (measurable_const.add measurable_id)).aestronglyMeasurable
      M (Filter.Eventually.of_forall fun z => hM (m+z))
  have hc : (∫ _ : EuclideanSpace ℝ d, F m ∂multivariateGaussian 0 A) = F m := by simp
  rw [← hc,← integral_sub hi (integrable_const _)]
  calc
    _ ≤ ∫ z : EuclideanSpace ℝ d, K*‖z‖^β ∂multivariateGaussian 0 A := by
      apply norm_integral_le_of_norm_le ((GaussianNormMoment.integrable _ hβ).const_mul K)
      exact Filter.Eventually.of_forall fun z => by
        simpa only [add_sub_cancel_left] using hH (m+z) m
    _ = K*(∫ z : EuclideanSpace ℝ d, ‖z‖^β ∂multivariateGaussian 0 A) := integral_const_mul _ _
    _ ≤ _ := (mul_le_mul_of_nonneg_left (GaussianNormMoment.bound A hA hV hAV hβ) hK).trans_eq (by ring)

end SHEStochastic.BanachGaussianDisplacement
