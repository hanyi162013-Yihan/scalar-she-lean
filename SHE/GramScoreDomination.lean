module

public import SHE.MeasurableGaussianScores

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.MeasurableGaussianScores
open Set MeasureTheory GaussianIncrement GaussianGramScore MeasurableGeneralizedInverse
open scoped InnerProductSpace

variable {n : ℕ} {G H : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Positive Gram domination gives the canonical inverse-score
inequality on the actual covariance range, even at singular ranks.
The proof factors the actual Riesz functional through the larger
covariance range and does not compare chosen matrix inverse entries. -/
theorem scoreVariance_le_of_gram_domination (v : Fin n → G) (w : Fin n → H)
    {ell : ℝ} (hell : 0 < ell)
    (hdom : ∀ z : State n,ell*‖featureSynthesis v z‖^2 ≤ ‖featureSynthesis w z‖^2)
    {d : State n} (hd : d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.gram ℝ v)).range) :
    scoreVariance (Matrix.gram ℝ w) d ≤ scoreVariance (Matrix.gram ℝ v) d / ell := by
  let m : G := featureSynthesis v (coefficient (Matrix.gram ℝ v) d)
  have hm : m ∈ (featureSynthesis v).range := LinearMap.mem_range_self _ _
  have hpair (z : State n) : inner ℝ (featureSynthesis v z) m = inner ℝ z d := by
    rw [featureSynthesis_inner,coefficient,generalizedInverse_on_range (Matrix.gram ℝ v) hd]
  have hV : scoreVariance (Matrix.gram ℝ v) d = ‖m‖^2 := physical_scoreVariance_eq v hm hpair
  let B : State n →ₗ[ℝ] ℝ := (innerSL ℝ d).toLinearMap
  have hB (z : State n) : ‖B z‖^2 ≤ ‖m‖^2*‖featureSynthesis v z‖^2 := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℝ) (featureSynthesis v z) m) 2
    rw [hpair] at hh
    simpa only [B,ContinuousLinearMap.coe_coe,innerSL_apply_apply,real_inner_comm,mul_pow,mul_comm] using hh
  obtain ⟨T,hT,hTC,_⟩ := ScalarRange.factorization_of_gram_dominance
    (featureSynthesis w) B (fun z => ‖featureSynthesis v z‖^2) hell (norm_nonneg m) hB hdom
  obtain ⟨a,ha,hpa,hna⟩ := ScalarRange.adjoint_representer (featureSynthesis w).range T (1:ℝ)
  have hpaira (z : State n) : inner ℝ (featureSynthesis w z) a = inner ℝ z d := by
    have he := hpa (featureSynthesis w z) (LinearMap.mem_range_self _ z)
    rw [hTC] at he
    simpa only [B,RCLike.inner_apply,conj_trivial,mul_one,one_mul,ContinuousLinearMap.coe_coe,
      innerSL_apply_apply,real_inner_comm] using he
  have hnorm : ‖a‖ ≤ ‖m‖/Real.sqrt ell := by
    simpa only [norm_one,mul_one] using hna.trans
      (mul_le_mul_of_nonneg_right hT (norm_nonneg (1:ℝ)))
  rw [physical_scoreVariance_eq w ha hpaira,hV]
  have hs := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  simpa only [div_pow,Real.sq_sqrt hell.le] using hs

end SHE.MeasurableGaussianScores
