module

public import SHEStochastic.MatrixNonlinearCoefficient
public import SHE.GaussianContinuity
public import Mathlib.Probability.Kernel.MeasurableIntegral
public import SHEStochastic.BanachGaussianCovarianceHolder
public import SHEStochastic.BanachGaussianDisplacement
public import SHEStochastic.BanachGaussianMeanHolder

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixGaussianAverage
open MeasureTheory ProbabilityTheory MatrixNonlinearCoefficient
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
variable {d : Type*} [Fintype d] [DecidableEq d]
variable (G : Coefficient d)

/-- The genuine coupled Gaussian covariance update: the entire diffusion
matrix is averaged at a vector mean and a full covariance matrix. -/
def average (C : Matrix d d ℝ) (m : EuclideanSpace ℝ d) : Matrix d d ℝ :=
  ∫ z, G.covariance (m+z) ∂multivariateGaussian 0 C

theorem integrable (C : Matrix d d ℝ) (m : EuclideanSpace ℝ d) :
    Integrable (fun z => G.covariance (m+z)) (multivariateGaussian 0 C) :=
  Integrable.of_bound (G.covariance_measurable.comp (measurable_const.add measurable_id)).aestronglyMeasurable
    ((G.bound : ℝ)^2) (Filter.Eventually.of_forall fun z => G.covariance_bound (m+z))

theorem norm_bound (C : Matrix d d ℝ) (m : EuclideanSpace ℝ d) :
    ‖average G C m‖ ≤ (G.bound : ℝ)^2 := by
  simpa only [average, probReal_univ, mul_one] using norm_integral_le_of_norm_le_const
    (μ := multivariateGaussian (0 : EuclideanSpace ℝ d) C)
    (Filter.Eventually.of_forall fun z => G.covariance_bound (m+z))

theorem elliptic (C : Matrix d d ℝ) (m : EuclideanSpace ℝ d) :
    G.lower • (1 : Matrix d d ℝ) ≤ average G C m ∧
      average G C m ≤ ((G.bound : ℝ)^2+1) • (1 : Matrix d d ℝ) := by
  constructor
  · have hh := integral_mono_ae
      (integrable_const (G.lower • (1 : Matrix d d ℝ))) (integrable G C m)
      (Filter.Eventually.of_forall fun z => G.lower_bound (m+z))
    rw [Matrix.le_iff] at hh
    change (average G C m-G.lower • (1 : Matrix d d ℝ)).PosSemidef
    convert! hh using 1 <;> simp only [average, integral_const, probReal_univ, one_smul]
  · have hh := integral_mono_ae (integrable G C m)
      (integrable_const (((G.bound : ℝ)^2+1) • (1 : Matrix d d ℝ)))
      (Filter.Eventually.of_forall fun z => G.covariance_upper (m+z))
    rw [Matrix.le_iff] at hh
    change (((G.bound : ℝ)^2+1) • (1 : Matrix d d ℝ)-average G C m).PosSemidef
    convert! hh using 1 <;> simp only [average, integral_const, probReal_univ, one_smul]

def kernel : Kernel (Matrix d d ℝ × EuclideanSpace ℝ d) (EuclideanSpace ℝ d) where
  toFun p := multivariateGaussian 0 p.1
  measurable' := measurable_multivariateGaussian.comp (measurable_const.prodMk measurable_fst)

instance kernel_markov : IsMarkovKernel (kernel (d := d)) where
  isProbabilityMeasure _ := by change IsProbabilityMeasure (multivariateGaussian 0 _); infer_instance

/-- The update is jointly Borel, including singular covariances and
merely measurable bounded coefficients. -/
theorem measurable : Measurable (fun p : Matrix d d ℝ × EuclideanSpace ℝ d => average G p.1 p.2) := by
  have hh : Measurable (fun p : (Matrix d d ℝ × EuclideanSpace ℝ d) × EuclideanSpace ℝ d =>
      G.covariance (p.1.2+p.2)) := G.covariance_measurable.comp (measurable_fst.snd.add measurable_snd)
  exact (hh.stronglyMeasurable.integral_kernel_prod_right' (κ := kernel (d := d))).measurable

theorem mean_holder {β K : ℝ}
    (hG : ∀ z w, ‖G.value z-G.value w‖ ≤ K*‖z-w‖^β)
    (C : Matrix d d ℝ) (m n : EuclideanSpace ℝ d) :
    ‖average G C m-average G C n‖ ≤ (2*(G.bound : ℝ)*K)*‖m-n‖^β := by
  rw [average, average, ← integral_sub (integrable G C m) (integrable G C n)]
  have hb (z : EuclideanSpace ℝ d) :
      ‖G.covariance (m+z)-G.covariance (n+z)‖ ≤ (2*(G.bound : ℝ)*K)*‖m-n‖^β := by
    simpa only [add_sub_add_right_eq_sub] using G.covariance_holder hG (m+z) (n+z)
  simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const
    (μ := multivariateGaussian (0 : EuclideanSpace ℝ d) C) (Filter.Eventually.of_forall hb)

/-- Reuse the proved Banach-valued Gaussian continuity theorem for
the full matrix update, including singular covariance limits. -/
theorem continuous {n : ℕ} (G : Coefficient (Fin n)) (hG : Continuous G.value) :
    Continuous (fun p : SHE.GaussianContinuity.PositiveCovariance n × EuclideanSpace ℝ (Fin n) =>
      average G p.1.val p.2) :=
  SHE.GaussianContinuity.continuous_gaussian_average G.covariance
    (hG.mul (continuous_star.comp hG)) G.covariance_bound

theorem covariance_lipschitz {n : ℕ} (G : Coefficient (Fin n)) {r K β : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (hG : ∀ z w, ‖G.value z-G.value w‖ ≤ K*‖z-w‖^β)
    (A C : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsotropicGaussianHolder.matrix r ≤ A) (hC : IsotropicGaussianHolder.matrix r ≤ C)
    (m : EuclideanSpace ℝ (Fin n)) :
    ‖average G A m-average G C m‖ ≤
      ((2*(G.bound : ℝ)*K)*SHE.GaussianAudit.secondScoreAbsIncrementMoment β*r^(β/2-1))*
        SHE.GaussianSignedCovariance.covarianceBoundConstant n*‖A-C‖ :=
  BanachGaussianCovarianceHolder.bound hr
    (mul_nonneg (mul_nonneg (by norm_num) G.bound.coe_nonneg) hK) hβ
    G.covariance G.covariance_measurable.stronglyMeasurable ((G.bound : ℝ)^2) G.covariance_bound
    (G.covariance_holder hG) A C hA hC m

theorem displacement {K β V : ℝ} (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (hG : ∀ z w, ‖G.value z-G.value w‖ ≤ K*‖z-w‖^β)
    (A : Matrix d d ℝ) (hA : 0 ≤ A) (hV : 0 ≤ V) (hAV : ‖A‖ ≤ V)
    (m : EuclideanSpace ℝ d) :
    ‖average G A m-G.covariance m‖ ≤
      (2*(G.bound : ℝ)*K)*V^(β/2)*GaussianNormMoment.moment d β :=
  BanachGaussianDisplacement.bound G.covariance G.covariance_measurable.stronglyMeasurable
    ((G.bound : ℝ)^2) G.covariance_bound
    (mul_nonneg (mul_nonneg (by norm_num) G.bound.coe_nonneg) hK) hβ
    (G.covariance_holder hG) A hA hV hAV m

theorem mean_lipschitz {n : ℕ} (G : Coefficient (Fin n)) {r K β : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (hG : ∀ z w, ‖G.value z-G.value w‖ ≤ K*‖z-w‖^β)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsotropicGaussianHolder.matrix r ≤ A)
    (z w : EuclideanSpace ℝ (Fin n)) :
    ‖average G A z-average G A w‖ ≤
      ((2*(G.bound : ℝ)*K)*GaussianNormMoment.moment (Fin n) (β+1)*r^((β-1)/2))*‖z-w‖ :=
  BanachGaussianMeanHolder.bound hr
    (mul_nonneg (mul_nonneg (by norm_num) G.bound.coe_nonneg) hK) hβ G.covariance
    G.covariance_measurable.stronglyMeasurable ((G.bound : ℝ)^2) G.covariance_bound
    (G.covariance_holder hG) A hA z w

end SHEStochastic.MatrixGaussianAverage
