module

public import SHE.MeasurableGaussianScores

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MeasurableGaussianScores
open Set MeasureTheory ProbabilityTheory GaussianIncrement MeasurableGeneralizedInverse
open scoped InnerProductSpace
variable {n : ℕ}

theorem firstScore_add (A : Mat n) (d e y : State n) :
    firstScore A (d + e) y = firstScore A d y + firstScore A e y := by
  simp only [firstScore, coefficient, map_add, inner_add_left]

theorem firstScore_smul (A : Mat n) (r : ℝ) (d y : State n) :
    firstScore A (r • d) y = r * firstScore A d y := by
  simp only [firstScore, coefficient, map_smul, real_inner_smul_left]

theorem scoreVariance_smul (A : Mat n) (r : ℝ) (d : State n) :
    scoreVariance A (r • d) = r ^ 2 * scoreVariance A d := by
  simp only [scoreVariance, coefficient, map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

theorem scoreVariance_parallelogram (A : Mat n) (d e : State n) :
    scoreVariance A (d + e) + scoreVariance A (d - e) = 2 * scoreVariance A d + 2 * scoreVariance A e := by
  simp only [scoreVariance, coefficient, map_add, map_sub, inner_add_left, inner_sub_left,
    inner_add_right, inner_sub_right]
  ring

theorem scoreVariance_add_le {A : Mat n} (hA : A.PosSemidef) {d e : State n}
    (hd : d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) A).range)
    (he : e ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) A).range) :
    scoreVariance A (d + e) ≤ 2 * scoreVariance A d + 2 * scoreVariance A e := by
  have hn := scoreVariance_nonneg hA (Submodule.sub_mem _ hd he)
  linarith [scoreVariance_parallelogram A d e]

theorem scoreVariance_sub_le {A : Mat n} (hA : A.PosSemidef) {d e : State n}
    (hd : d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) A).range)
    (he : e ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) A).range) :
    scoreVariance A (d - e) ≤ 2 * scoreVariance A d + 2 * scoreVariance A e := by
  have hn := scoreVariance_nonneg hA (Submodule.add_mem _ hd he)
  linarith [scoreVariance_parallelogram A d e]

end SHE.MeasurableGaussianScores
