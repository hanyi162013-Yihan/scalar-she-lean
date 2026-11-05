module

public import SHE.MeasurableGeneralizedInverse

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-! Literal Borel first and second Gaussian score fields for varying finite
covariances. Their physical energies are independent of the conditioning of
the selected inverse, including covariance collisions and rank changes. -/
namespace SHE.MeasurableGaussianScores
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianAudit
  GaussianGramScore MeasurableGeneralizedInverse
open scoped InnerProductSpace

variable {n : ℕ}

def coefficient (A : Mat n) (d : State n) : State n := generalizedInverse A d

def firstScore (A : Mat n) (d y : State n) : ℝ := inner ℝ (coefficient A d) y

def scoreVariance (A : Mat n) (d : State n) : ℝ := inner ℝ (coefficient A d) d

def secondScore (A : Mat n) (d y : State n) : ℝ :=
  firstScore A d y ^ 2 - scoreVariance A d

theorem coefficient_measurable :
    Measurable (fun p : Mat n × State n => coefficient p.1 p.2) :=
  generalizedInverse_measurable

theorem firstScore_measurable :
    Measurable (fun p : (Mat n × State n) × State n => firstScore p.1.1 p.1.2 p.2) := by
  exact continuous_inner.measurable.comp
    ((coefficient_measurable.comp measurable_fst).prodMk measurable_snd)

theorem scoreVariance_measurable :
    Measurable (fun p : Mat n × State n => scoreVariance p.1 p.2) := by
  exact continuous_inner.measurable.comp (coefficient_measurable.prodMk measurable_snd)

theorem secondScore_measurable :
    Measurable (fun p : (Mat n × State n) × State n => secondScore p.1.1 p.1.2 p.2) := by
  exact firstScore_measurable.pow_const 2 |>.sub
    (scoreVariance_measurable.comp measurable_fst)

theorem firstScore_mean_zero (A : Mat n) (d : State n) :
    (∫ y, firstScore A d y ∂multivariateGaussian 0 A) = 0 :=
  gaussian_inner_mean_zero A (coefficient A d)

theorem firstScore_response {A : Mat n} (hA : A.PosSemidef) {d : State n}
    (hd : d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) A).range) :
    covarianceResponse (multivariateGaussian 0 A) (innerSL ℝ (coefficient A d)) = d := by
  rw [gaussian_inner_covarianceResponse hA]
  exact generalizedInverse_on_range A hd

theorem firstScore_variance {A : Mat n} (hA : A.PosSemidef) {d : State n}
    (hd : d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) A).range) :
    Var[innerSL ℝ (coefficient A d); multivariateGaussian 0 A] = scoreVariance A d := by
  rw [gaussian_inner_variance hA]
  change inner ℝ (coefficient A d) (Matrix.toEuclideanCLM (𝕜 := ℝ) A (generalizedInverse A d)) = _
  rw [generalizedInverse_on_range A hd]
  rfl

theorem scoreVariance_nonneg {A : Mat n} (hA : A.PosSemidef) {d : State n}
    (hd : d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) A).range) :
    0 ≤ scoreVariance A d := by
  rw [← firstScore_variance hA hd]
  exact variance_nonneg _ _

theorem firstScore_even_moments {A : Mat n} (hA : A.PosSemidef) {d : State n}
    (hd : d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) A).range) (p : ℕ) :
    Integrable (fun y => |firstScore A d y| ^ (2 * p)) (multivariateGaussian 0 A) ∧
      (∫ y, |firstScore A d y| ^ (2 * p) ∂multivariateGaussian 0 A) =
        scoreVariance A d ^ p * firstScoreMoment p := by
  have h := gaussian_projection_even_moment (multivariateGaussian (0 : State n) A)
    (innerSL ℝ (coefficient A d)) p
  rw [gaussian_inner_mean_zero, firstScore_variance hA hd] at h
  simpa only [sub_zero, firstScore, innerSL_apply_apply] using h

theorem secondScore_even_moments {A : Mat n} (hA : A.PosSemidef) {d : State n}
    (hd : d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) A).range) (p : ℕ) :
    Integrable (fun y => |secondScore A d y| ^ (2 * p)) (multivariateGaussian 0 A) ∧
      (∫ y, |secondScore A d y| ^ (2 * p) ∂multivariateGaussian 0 A) =
        scoreVariance A d ^ (2 * p) * secondScoreMoment p := by
  have h := gaussian_projection_covariance_score_even_moment
    (multivariateGaussian (0 : State n) A) (innerSL ℝ (coefficient A d)) p
  rw [gaussian_inner_mean_zero, firstScore_variance hA hd] at h
  simpa only [sub_zero, secondScore, firstScore, innerSL_apply_apply] using h

theorem secondScore_mean_zero {A : Mat n} (hA : A.PosSemidef) {d : State n}
    (hd : d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) A).range) :
    (∫ y, secondScore A d y ∂multivariateGaussian 0 A) = 0 := by
  let ℓ := innerSL ℝ (coefficient A d)
  have hm : (∫ y, ℓ y ∂multivariateGaussian 0 A) = 0 := firstScore_mean_zero A d
  have h := integral_gaussian_mixed_score (multivariateGaussian (0 : State n) A) ℓ ℓ hm hm
  rw [covariance_self (by fun_prop), firstScore_variance hA hd] at h
  convert! h using 1
  congr 1
  funext y
  change firstScore A d y ^ 2 - scoreVariance A d = ℓ y * ℓ y - scoreVariance A d
  rw [pow_two]
  rfl

theorem firstScore_moment_bound {A : Mat n} (hA : A.PosSemidef) {d : State n}
    (hd : d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) A).range) {B : ℝ}
    (hB : scoreVariance A d ≤ B) (p : ℕ) :
    (∫ y, |firstScore A d y| ^ (2 * p) ∂multivariateGaussian 0 A) ≤
      B ^ p * firstScoreMoment p := by
  rw [(firstScore_even_moments hA hd p).2]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (scoreVariance_nonneg hA hd) hB p) (firstScoreMoment_nonneg p)

theorem secondScore_moment_bound {A : Mat n} (hA : A.PosSemidef) {d : State n}
    (hd : d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) A).range) {B : ℝ}
    (hB : scoreVariance A d ≤ B) (p : ℕ) :
    (∫ y, |secondScore A d y| ^ (2 * p) ∂multivariateGaussian 0 A) ≤
      B ^ (2 * p) * secondScoreMoment p := by
  rw [(secondScore_even_moments hA hd p).2]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (scoreVariance_nonneg hA hd) hB (2 * p)) (secondScoreMoment_nonneg p)

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]

theorem physical_direction_mem_range (v : Fin n → G) {d : State n} {m : G}
    (hm : m ∈ (featureSynthesis v).range)
    (hpair : ∀ a : State n, inner ℝ (featureSynthesis v a) m = inner ℝ a d) :
    d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.gram ℝ v)).range := by
  obtain ⟨a, ha, _⟩ := physical_direction_is_covarianceResponse v hm hpair
  rw [gaussian_inner_covarianceResponse (Matrix.posSemidef_gram ℝ v)] at ha
  exact ⟨a, ha⟩

/-- The measurable inverse gives exactly the actual physical Riesz vector
after synthesis. Its possibly large Euclidean coefficients do not enter the
Gaussian score energy. -/
theorem coefficient_synthesis_eq (v : Fin n → G) {d : State n} {m : G}
    (hm : m ∈ (featureSynthesis v).range)
    (hpair : ∀ a : State n, inner ℝ (featureSynthesis v a) m = inner ℝ a d) :
    featureSynthesis v (coefficient (Matrix.gram ℝ v) d) = m := by
  let A := Matrix.gram ℝ v
  let x := coefficient A d
  have hx : Matrix.toEuclideanCLM (𝕜 := ℝ) A x = d :=
    generalizedInverse_on_range A (physical_direction_mem_range v hm hpair)
  obtain ⟨b, hb⟩ := hm
  have hbA : Matrix.toEuclideanCLM (𝕜 := ℝ) A b = d := by
    apply ext_inner_left ℝ
    intro z
    rw [← featureSynthesis_inner, hb, hpair]
  have hzero : ‖featureSynthesis v (x - b)‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq, featureSynthesis_inner, map_sub, hx, hbA,
      sub_self, inner_zero_right]
  have heq : featureSynthesis v (x - b) = 0 := by
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hzero)
  rw [map_sub, sub_eq_zero] at heq
  exact heq.trans hb

theorem physical_scoreVariance_eq (v : Fin n → G) {d : State n} {m : G}
    (hm : m ∈ (featureSynthesis v).range)
    (hpair : ∀ a : State n, inner ℝ (featureSynthesis v a) m = inner ℝ a d) :
    scoreVariance (Matrix.gram ℝ v) d = ‖m‖ ^ 2 := by
  rw [← firstScore_variance (Matrix.posSemidef_gram ℝ v)
    (physical_direction_mem_range v hm hpair), gaussian_gram_variance,
    coefficient_synthesis_eq v hm hpair]

/-- Exact all-order moments of the literal jointly Borel score fields, with
the actual physical Riesz energy and no Gram conditioning factor. -/
theorem physical_score_moments (v : Fin n → G) {d : State n} {m : G}
    (hm : m ∈ (featureSynthesis v).range)
    (hpair : ∀ a : State n, inner ℝ (featureSynthesis v a) m = inner ℝ a d) (p : ℕ) :
    Integrable (fun y => |firstScore (Matrix.gram ℝ v) d y| ^ (2 * p))
        (multivariateGaussian 0 (Matrix.gram ℝ v)) ∧
      (∫ y, |firstScore (Matrix.gram ℝ v) d y| ^ (2 * p)
        ∂multivariateGaussian 0 (Matrix.gram ℝ v)) = ‖m‖ ^ (2 * p) * firstScoreMoment p ∧
    Integrable (fun y => |secondScore (Matrix.gram ℝ v) d y| ^ (2 * p))
        (multivariateGaussian 0 (Matrix.gram ℝ v)) ∧
      (∫ y, |secondScore (Matrix.gram ℝ v) d y| ^ (2 * p)
        ∂multivariateGaussian 0 (Matrix.gram ℝ v)) = ‖m‖ ^ (4 * p) * secondScoreMoment p := by
  have hd := physical_direction_mem_range v hm hpair
  have h₁ := firstScore_even_moments (Matrix.posSemidef_gram ℝ v) hd p
  have h₂ := secondScore_even_moments (Matrix.posSemidef_gram ℝ v) hd p
  rw [physical_scoreVariance_eq v hm hpair] at h₁ h₂
  simp only [← pow_mul] at h₁ h₂
  refine ⟨h₁.1, h₁.2, h₂.1, ?_⟩
  simpa only [show 2 * (2 * p) = 4 * p by omega] using h₂.2

end SHE.MeasurableGaussianScores
