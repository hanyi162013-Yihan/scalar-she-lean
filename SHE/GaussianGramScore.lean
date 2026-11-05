module

public import SHE.GaussianHessianScore
public import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-! Actual Gaussian scores for arbitrary finite Hilbert-space covariance
features. The physical direction is identified by its genuine Riesz
pairing; singular observation Grams and collisions are permitted. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.GaussianGramScore
open MeasureTheory ProbabilityTheory Set Real Matrix SHE.GaussianAudit
  SHE.GaussianSmooth SHE.GaussianHessianScore SHE.GaussianIncrement
open scoped InnerProductSpace Matrix.Norms.L2Operator

theorem gaussian_inner_mean_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (a : State n) :
    (∫ x : State n, innerSL ℝ a x ∂multivariateGaussian 0 A) = 0 := by
  have h := (innerSL ℝ a).integral_comp_comm
    (IsGaussian.integrable_id (μ := multivariateGaussian (0 : State n) A))
  simpa only [id_eq, integral_id_multivariateGaussian, map_zero] using h

theorem gaussian_inner_variance {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (a : State n) :
    Var[innerSL ℝ a; multivariateGaussian 0 A] = inner ℝ a (Matrix.toEuclideanCLM (𝕜 := ℝ) A a) := by
  have h := covarianceBilin_self
    (IsGaussian.memLp_two_id (μ := multivariateGaussian (0 : State n) A)) a
  rw [covarianceBilin_multivariateGaussian hA] at h
  rw [Matrix.inner_toEuclideanCLM]
  exact h.symm

theorem gaussian_inner_covarianceResponse {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (a : State n) :
    covarianceResponse (multivariateGaussian 0 A) (innerSL ℝ a) = Matrix.toEuclideanCLM (𝕜 := ℝ) A a := by
  apply ext_inner_left ℝ
  intro b
  have h := covarianceResponse_duality (multivariateGaussian 0 A) (innerSL ℝ a) (innerSL ℝ b)
  have hc := covarianceBilin_apply_eq_cov
    (IsGaussian.memLp_two_id (μ := multivariateGaussian (0 : State n) A)) b a
  rw [covarianceBilin_multivariateGaussian hA] at hc
  rw [Matrix.inner_toEuclideanCLM]
  exact h.trans hc.symm

variable {n : ℕ} {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]

def featureSynthesis (v : Fin n → G) : State n →ₗ[ℝ] G where
  toFun a := ∑ i, a i • v i
  map_add' a b := by simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [PiLp.smul_apply, smul_smul, Finset.smul_sum, RingHom.id_apply, smul_eq_mul]

theorem featureSynthesis_inner (v : Fin n → G) (a b : State n) :
    inner ℝ (featureSynthesis v a) (featureSynthesis v b) =
      inner ℝ a (Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.gram ℝ v) b) := by
  change inner ℝ (∑ i, a i • v i) (∑ i, b i • v i) = _
  rw [Matrix.inner_toEuclideanCLM]
  have h := Matrix.star_dotProduct_gram_mulVec v (fun i => a i) (fun i => b i)
  simpa only [star_trivial] using h.symm

theorem gaussian_gram_variance (v : Fin n → G) (a : State n) :
    Var[innerSL ℝ a; multivariateGaussian 0 (Matrix.gram ℝ v)] = ‖featureSynthesis v a‖ ^ 2 := by
  rw [gaussian_inner_variance (Matrix.posSemidef_gram ℝ v), ← featureSynthesis_inner,
    real_inner_self_eq_norm_sq]

/-- Every genuine covariance-range Riesz direction is the covariance
response of an actual Gaussian scalar observation, with variance exactly
the squared physical representative norm. -/
theorem physical_direction_is_covarianceResponse (v : Fin n → G) {d : State n} {m : G}
    (hm : m ∈ (featureSynthesis v).range)
    (hpair : ∀ a : State n, inner ℝ (featureSynthesis v a) m = inner ℝ a d) :
    ∃ a : State n,
      covarianceResponse (multivariateGaussian 0 (Matrix.gram ℝ v)) (innerSL ℝ a) = d ∧
      Var[innerSL ℝ a; multivariateGaussian 0 (Matrix.gram ℝ v)] = ‖m‖ ^ 2 := by
  obtain ⟨a, ha⟩ := hm
  refine ⟨a, ?_, ?_⟩
  · rw [gaussian_inner_covarianceResponse (Matrix.posSemidef_gram ℝ v)]
    apply ext_inner_left ℝ
    intro b
    rw [← featureSynthesis_inner, ha, hpair]
  · rw [gaussian_gram_variance, ha]

/-- The covariance-normalized physical Hessian has the positive leverage
bound for the actual Gaussian Gram law, without a conditioning constant. -/
theorem hessian_gaussian_gram_physical_bound (v : Fin n → G) {d : State n} {m : G}
    (hm : m ∈ (featureSynthesis v).range)
    (hpair : ∀ a : State n, inner ℝ (featureSynthesis v a) m = inner ℝ a d)
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L B : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ B) (z : State n) :
    |fderiv ℝ (fderiv ℝ (average (multivariateGaussian 0 (Matrix.gram ℝ v)) F)) z d d| ≤
      2 * M * ‖m‖ ^ 2 := by
  obtain ⟨a, ha, hvar⟩ := physical_direction_is_covarianceResponse v hm hpair
  have h := hessian_average_covarianceResponse_bound (multivariateGaussian 0 (Matrix.gram ℝ v))
    (innerSL ℝ a) (gaussian_inner_mean_zero _ a) hF hbound hD hDD z
  rwa [ha, hvar] at h

/-- The physical Riesz vector controls every fixed moment of the actual
first and second Gaussian scores, with exact scalar Gaussian constants.
There is no Gram-conditioning factor, also at singular ranks. -/
theorem physical_gaussian_score_moments (v : Fin n → G) {d : State n} {m : G}
    (hm : m ∈ (featureSynthesis v).range)
    (hpair : ∀ a : State n, inner ℝ (featureSynthesis v a) m = inner ℝ a d) :
    ∃ ℓ : State n →L[ℝ] ℝ,
      (∫ y, ℓ y ∂multivariateGaussian 0 (Matrix.gram ℝ v)) = 0 ∧
      covarianceResponse (multivariateGaussian 0 (Matrix.gram ℝ v)) ℓ = d ∧
      (∀ p : ℕ,
        Integrable (fun y => |ℓ y| ^ (2 * p)) (multivariateGaussian 0 (Matrix.gram ℝ v)) ∧
        (∫ y, |ℓ y| ^ (2 * p) ∂multivariateGaussian 0 (Matrix.gram ℝ v)) =
          ‖m‖ ^ (2 * p) * firstScoreMoment p) ∧
      (∀ p : ℕ,
        Integrable (fun y => |(ℓ y) ^ 2 - ‖m‖ ^ 2| ^ (2 * p))
          (multivariateGaussian 0 (Matrix.gram ℝ v)) ∧
        (∫ y, |(ℓ y) ^ 2 - ‖m‖ ^ 2| ^ (2 * p) ∂multivariateGaussian 0 (Matrix.gram ℝ v)) =
          ‖m‖ ^ (4 * p) * secondScoreMoment p) := by
  obtain ⟨a, ha, hvar⟩ := physical_direction_is_covarianceResponse v hm hpair
  let μ := multivariateGaussian (0 : State n) (Matrix.gram ℝ v)
  let ℓ := innerSL ℝ a
  have hmean : (∫ y, ℓ y ∂μ) = 0 := gaussian_inner_mean_zero _ a
  refine ⟨ℓ, hmean, ha, ?_, ?_⟩
  · intro p
    have h := gaussian_projection_even_moment μ ℓ p
    rw [hmean, hvar] at h
    simp only [sub_zero, ← pow_mul] at h
    exact h
  · intro p
    have h := gaussian_projection_covariance_score_even_moment μ ℓ p
    rw [hmean, hvar] at h
    simp only [sub_zero, ← pow_mul] at h
    simpa only [show 2 * (2 * p) = 4 * p by omega] using h

/-- The genuine signed covariance-profile mark is bounded by its actual
positive covariance leverage. The signed input remains inside the
continuum integral throughout the estimate. -/
theorem covariance_mark_positive_bound {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (v : Fin n → G) (d : X → State n) (m : X → G)
    (hm : ∀ x, m x ∈ (featureSynthesis v).range)
    (hpair : ∀ x a, inner ℝ (featureSynthesis v a) (m x) = inner ℝ a (d x))
    (e : X → ℝ)
    (hi : Integrable (fun x => e x • SHE.GaussianProfileMark.rankMatrix (d x)) μ)
    (hweight : Integrable (fun x => |e x| * ‖m x‖ ^ 2) μ)
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L B : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ B) (z : State n) :
    |(1 / 2 : ℝ) * SHE.GaussianTaylorAverage.covarianceAction
      (SHE.GaussianProfileMark.profileCovariance μ e d)
      (fderiv ℝ (fderiv ℝ (average (multivariateGaussian 0 (Matrix.gram ℝ v)) F)) z)| ≤
      M * ∫ x, |e x| * ‖m x‖ ^ 2 ∂μ := by
  let H := fderiv ℝ (fderiv ℝ (average (multivariateGaussian 0 (Matrix.gram ℝ v)) F)) z
  have hM : 0 ≤ M := (norm_nonneg (F 0)).trans (hbound 0)
  have hH (x : X) : |H (d x) (d x)| ≤ 2 * M * ‖m x‖ ^ 2 :=
    hessian_gaussian_gram_physical_bound v (hm x) (hpair x) hF hbound hD hDD z
  have hpoint (x : X) : ‖e x * H (d x) (d x)‖ ≤ (2 * M) * (|e x| * ‖m x‖ ^ 2) := by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h := mul_le_mul_of_nonneg_left (hH x) (abs_nonneg (e x))
    convert! h using 1
    ring
  have hh := norm_integral_le_of_norm_le (hweight.const_mul (2 * M))
    (Filter.Eventually.of_forall hpoint)
  rw [integral_const_mul] at hh
  rw [SHE.GaussianProfileMark.profileCovariance_action μ e d hi]
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  change (1 / 2 : ℝ) * |∫ x, e x * H (d x) (d x) ∂μ| ≤ _
  have h := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 1 / 2)
  convert! h using 1
  ring

end SHE.GaussianGramScore
