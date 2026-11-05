module

public import SHE.MeasurableGaussianScores
public import SHE.PositiveMatrixRanges

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
noncomputable section

namespace SHE.MeasurableGaussianScores
open GaussianIncrement MeasurableGeneralizedInverse
open scoped InnerProductSpace
variable {n : ℕ} {A T : Mat n}

/-- Canonical score energy is antitone under arbitrary PSD matrix
domination, including singular ranks. No inverse conditioning is used. -/
theorem scoreVariance_antitone_matrix (hA : A.PosSemidef) (hT : T.PosSemidef)
    (hAT : (T-A).PosSemidef) {d : State n}
    (hd : d∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range) :
    scoreVariance T d≤scoreVariance A d := by
  have hdt:d∈(Matrix.toEuclideanCLM (𝕜:=ℝ) T).range:=
    PositiveMatrixRanges.range_le_of_domination hT hA 1 (by simpa only [one_smul] using hAT) hd
  let a:=coefficient A d
  let b:=coefficient T d
  have ha:Matrix.toEuclideanCLM (𝕜:=ℝ) A a=d:=generalizedInverse_on_range A hd
  have hb:Matrix.toEuclideanCLM (𝕜:=ℝ) T b=d:=generalizedInverse_on_range T hdt
  have hq : 0 ≤ inner ℝ (a-b) (Matrix.toEuclideanCLM (𝕜:=ℝ) A (a-b)) := by
    rw [Matrix.inner_toEuclideanCLM]
    simpa only [star_trivial] using hA.dotProduct_mulVec_nonneg (WithLp.ofLp (a-b))
  have hr : 0 ≤ inner ℝ b (Matrix.toEuclideanCLM (𝕜:=ℝ) (T-A) b) := by
    rw [Matrix.inner_toEuclideanCLM]
    simpa only [star_trivial] using hAT.dotProduct_mulVec_nonneg (WithLp.ofLp b)
  have hs:inner ℝ a (Matrix.toEuclideanCLM (𝕜:=ℝ) A b)=inner ℝ b d:=by
    have hh:=(Matrix.isSymmetric_toEuclideanLin_iff.mpr hA.isHermitian) a b
    change inner ℝ (Matrix.toEuclideanCLM (𝕜:=ℝ) A a) b=inner ℝ a (Matrix.toEuclideanCLM (𝕜:=ℝ) A b) at hh
    rw [ha,real_inner_comm] at hh
    exact hh.symm
  have he:Matrix.toEuclideanCLM (𝕜:=ℝ) (T-A) b=
      Matrix.toEuclideanCLM (𝕜:=ℝ) T b-Matrix.toEuclideanCLM (𝕜:=ℝ) A b:=by
    rw [map_sub]
    rfl
  rw [map_sub,ha,inner_sub_left,inner_sub_right,inner_sub_right,hs] at hq
  rw [he,hb,inner_sub_right] at hr
  change inner ℝ b d ≤ inner ℝ a d
  linarith

end SHE.MeasurableGaussianScores
