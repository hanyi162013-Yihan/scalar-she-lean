module

public import SHE.GramScoreDomination

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.MeasurableGaussianScores
open Set GaussianIncrement GaussianGramScore MeasurableGeneralizedInverse
open scoped InnerProductSpace
variable {n : ℕ} {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]

abbrev FrameIndex (v : Fin n → G) := Fin (Module.finrank ℝ (featureSynthesis v).range)

def frameCoefficients (v : Fin n → G) (k : FrameIndex v) : State n :=
  Classical.choose ((stdOrthonormalBasis ℝ (featureSynthesis v).range) k).property

theorem frameCoefficients_image (v : Fin n → G) (k : FrameIndex v) :
    featureSynthesis v (frameCoefficients v k) =
      ((stdOrthonormalBasis ℝ (featureSynthesis v).range) k : G) :=
  Classical.choose_spec ((stdOrthonormalBasis ℝ (featureSynthesis v).range) k).property

theorem frameCoefficients_orthonormal (v : Fin n → G) :
    Orthonormal ℝ (fun k => featureSynthesis v (frameCoefficients v k)) := by
  simp_rw [frameCoefficients_image]
  refine ⟨?_,?_⟩
  · intro k
    exact (stdOrthonormalBasis ℝ (featureSynthesis v).range).orthonormal.norm_eq_one k
  · intro k l hkl
    exact (stdOrthonormalBasis ℝ (featureSynthesis v).range).orthonormal.inner_eq_zero hkl

theorem frame_card_le (v : Fin n → G) : Fintype.card (FrameIndex v) ≤ n := by
  have hh := LinearIndependent.of_comp (featureSynthesis v) (frameCoefficients_orthonormal v).linearIndependent
  simpa using hh.fintype_card_le_finrank

/-- Canonical inverse-score energy is precisely the real covariance
range-frame leverage, including every singular Gram configuration. -/
theorem scoreVariance_eq_frame (v : Fin n → G) {d : State n}
    (hd : d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.gram ℝ v)).range) :
    scoreVariance (Matrix.gram ℝ v) d =
      ∑ k : FrameIndex v,(inner ℝ (frameCoefficients v k) d)^2 := by
  let m : G := featureSynthesis v (coefficient (Matrix.gram ℝ v) d)
  have hm : m ∈ (featureSynthesis v).range := LinearMap.mem_range_self _ _
  have hp (z : State n) : inner ℝ (featureSynthesis v z) m = inner ℝ z d := by
    rw [featureSynthesis_inner,coefficient,generalizedInverse_on_range (Matrix.gram ℝ v) hd]
  rw [physical_scoreVariance_eq v hm hp]
  let b := stdOrthonormalBasis ℝ (featureSynthesis v).range
  let m' : (featureSynthesis v).range := ⟨m,hm⟩
  have he := b.sum_sq_norm_inner_right m'
  have hi (k : FrameIndex v) : inner ℝ (b k) m' = inner ℝ (frameCoefficients v k) d := by
    change inner ℝ (b k : G) m = _
    rw [← frameCoefficients_image]
    exact hp _
  simpa only [hi,Real.norm_eq_abs,sq_abs] using! he.symm

end SHE.MeasurableGaussianScores
