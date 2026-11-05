module

public import SHE.GaussianLaplaceSmooth
public import SHE.MeasurableGaussianScores

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-! Actual Gaussian smoothing of bounded Borel tests on the physical
covariance range. A smooth extension to the ambient finite-dimensional
space is constructed even when the original Gaussian is singular. -/
namespace SHE.GaussianRangeSmooth
open MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAudit
  GaussianGramScore MeasurableGeneralizedInverse GaussianConvolution
open scoped InnerProductSpace
variable {n : ℕ}

def liftedAverage (A : Mat n) (F : State n → ℝ) (a : State n) : ℝ :=
  gaussianAverage A F (Matrix.toEuclideanCLM (𝕜 := ℝ) A a)

theorem liftedAverage_likelihood {A : Mat n} (hA : A.PosSemidef)
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ y, |F y| ≤ M) (a : State n) :
    liftedAverage A F a = exp (-(inner ℝ a (Matrix.toEuclideanCLM (𝕜 := ℝ) A a)) / 2) *
      GaussianLaplaceSmooth.transform (multivariateGaussian 0 A) F a := by
  have h := gaussian_covarianceResponse_mean_likelihood_all (multivariateGaussian 0 A)
    (innerSL ℝ a) (gaussian_inner_mean_zero A a) F hF M hM 1
  rw [gaussian_inner_covarianceResponse hA, gaussian_inner_variance hA] at h
  simp only [one_smul, one_mul, one_pow, innerSL_apply_apply] at h
  change (∫ y, F (Matrix.toEuclideanCLM (𝕜 := ℝ) A a + y) ∂multivariateGaussian 0 A) = _
  rw [show (∫ y, F (Matrix.toEuclideanCLM (𝕜 := ℝ) A a + y) ∂multivariateGaussian 0 A) =
      ∫ y, F (y + Matrix.toEuclideanCLM (𝕜 := ℝ) A a) ∂multivariateGaussian 0 A by
        apply integral_congr_ae
        apply ae_of_all
        intro y
        change F (Matrix.toEuclideanCLM (𝕜 := ℝ) A a + y) = F (y + Matrix.toEuclideanCLM (𝕜 := ℝ) A a)
        rw [add_comm]]
  rw [h, GaussianLaplaceSmooth.transform, ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro y
  change F y * exp (inner ℝ a y - inner ℝ a (Matrix.toEuclideanCLM (𝕜 := ℝ) A a) / 2) =
    exp (-(inner ℝ a (Matrix.toEuclideanCLM (𝕜 := ℝ) A a)) / 2) * (exp (inner ℝ a y) • F y)
  rw [sub_eq_add_neg, exp_add]
  simp only [smul_eq_mul]
  rw [show -(inner ℝ a (Matrix.toEuclideanCLM (𝕜 := ℝ) A a) / 2) =
      -(inner ℝ a (Matrix.toEuclideanCLM (𝕜 := ℝ) A a)) / 2 by ring]
  ring

theorem contDiff_liftedAverage {A : Mat n} (hA : A.PosSemidef)
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ y, |F y| ≤ M) (k : ℕ) :
    ContDiff ℝ k (liftedAverage A F) := by
  have hM0 : 0 ≤ M := (abs_nonneg (F 0)).trans (hM 0)
  have hbound : ∀ y, ‖F y‖ ≤ M * exp (0 * ‖y‖) := by simpa using hM
  have hl := GaussianLaplaceSmooth.contDiff_transform k (multivariateGaussian 0 A)
    hF.stronglyMeasurable hM0 hbound
  have hq : ContDiff ℝ k (fun a : State n => inner ℝ a (Matrix.toEuclideanCLM (𝕜 := ℝ) A a)) :=
    contDiff_id.inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) A).contDiff
  have he : liftedAverage A F = fun a =>
      exp (-(inner ℝ a (Matrix.toEuclideanCLM (𝕜 := ℝ) A a)) / 2) *
        GaussianLaplaceSmooth.transform (multivariateGaussian 0 A) F a :=
    funext (liftedAverage_likelihood hA F hF M hM)
  rw [he]
  exact (hq.neg.div_const 2).exp.mul hl

def roughAverageExtension (A : Mat n) (F : State n → ℝ) (z : State n) : ℝ :=
  liftedAverage A F (generalizedInverse A z)

theorem contDiff_roughAverageExtension {A : Mat n} (hA : A.PosSemidef)
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ y, |F y| ≤ M) (k : ℕ) :
    ContDiff ℝ k (roughAverageExtension A F) := by
  exact (contDiff_liftedAverage hA F hF M hM k).comp
    (generalizedInverse A).toContinuousLinearMap.contDiff

/-- The extension is the literal Gaussian average at every physical
covariance-range mean, without requiring an invertible covariance. -/
theorem extension_eq_average_on_range (A : Mat n) (F : State n → ℝ) {z : State n}
    (hz : z ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) A).range) :
    roughAverageExtension A F z = gaussianAverage A F z := by
  unfold roughAverageExtension liftedAverage
  rw [generalizedInverse_on_range A hz]

theorem extension_bound (A : Mat n) (F : State n → ℝ) (M : ℝ)
    (hM : ∀ y, |F y| ≤ M) (z : State n) : |roughAverageExtension A F z| ≤ M := by
  have hb : ∀ y, ‖F y‖ ≤ M := by simpa only [Real.norm_eq_abs] using hM
  exact GaussianSmooth.average_norm_bound (multivariateGaussian 0 A) hb _

end SHE.GaussianRangeSmooth
