module

public import SHE.GaussianFixedScore
public import SHE.UncutSmoothWords

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.RecursiveGaussianScores
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion
open CutoffWordLevel CutoffWordHistories CutoffCarriers CutoffInsertionCore
open GaussianConvolution SmoothCylinders SmoothWords MeasurableGaussianScores
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

/-- The actual uncut recursive words retain bounded derivatives at each
fixed history. No uniformity in the time gaps is asserted here. -/
theorem test_boundedSmooth (k : ℕ) (p : History P k) :
    BoundedSmooth (UncutSmoothWords.test L k p) := by
  induction k with
  | zero => exact L.test_uniform.boundedSmooth p
  | succ k ih =>
    have hG := (ih p.1).average
      (multivariateGaussian (0 : WordRecursion.State (n+k)) ((carrier L k).nodeCovariance p).val)
    have hcoef := (R.totalVariance_smooth.comp_right (headProjection (n+k))).sub
      (BoundedSmooth.const (R.reference ((carrier L k).nodeTime p,p.2.2)))
    have hdir := (directionalSecond_boundedSmooth hG (row L k p)).comp_right
      (tailProjection (n+k))
    exact ((BoundedSmooth.const (1 / 2 : ℝ)).mul hcoef).mul hdir

/-- Each covariance split is recorded on the original growing state
space, without identifying observations at different insertion times. -/
abbrev Covariances := (k : ℕ) → History P (k+1) → MeasurableGeneralizedInverse.Mat (n+k)

/-- Exact old-score kernel recursion with the original newest-coordinate
coefficient and baseline at every node. -/
def scored (old residual : Covariances (P := P) (n := n)) :
    (k : ℕ) → History P k → WordRecursion.State (n+k) → ℝ
  | 0 => L.test
  | k+1 => fun p z =>
      (1 / 2 : ℝ) * (R.totalVariance (z 0) - R.reference ((carrier L k).nodeTime p,p.2.2)) *
        ∫ x, ∫ y, scored old residual k p.1 (tailProjection (n+k) z + x + y) *
          secondScore (old k p) (row L k p) x
          ∂multivariateGaussian 0 (residual k p) ∂multivariateGaussian 0 (old k p)

/-- The needed range condition is imposed only along the selected finite
history. In applications it is proved for almost every physical spatial
history, rather than required at colliding exceptional points. -/
def Supported (old residual : Covariances (P := P) (n := n)) :
    (k : ℕ) → History P k → Prop
  | 0 => fun _ => True
  | k+1 => fun p => Supported old residual k p.1 ∧
      (old k p).PosSemidef ∧ (residual k p).PosSemidef ∧
      ((carrier L k).nodeCovariance p).val = old k p + residual k p ∧
      row L k p ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (old k p)).range

/-- Every finite actual recursive word is exactly its iterated old-score
integral on supported histories. The proof substitutes the original test
at each node before using the induction hypothesis, and does not
differentiate a score integral or assume its derivatives are bounded. -/
theorem test_eq_scored (old residual : Covariances (P := P) (n := n))
    (k : ℕ) (p : History P k) (hp : Supported L old residual k p) :
    UncutSmoothWords.test L k p = scored L old residual k p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨hprev, ho, hr, he, hd⟩ := hp
    have hi := ih p.1 hprev
    funext z
    change (1 / 2 : ℝ) * (R.totalVariance (z 0) - R.reference ((carrier L k).nodeTime p,p.2.2)) *
        directionalSecond
          (gaussianAverage ((carrier L k).nodeCovariance p).val (UncutSmoothWords.test L k p.1))
          (tailProjection (n+k) z) (row L k p) = _
    rw [he, GaussianFixedScore.hessian_split_score ho hr (test_boundedSmooth L k p.1)
      (tailProjection (n+k) z) hd, hi]
    rfl

end SHE.RecursiveGaussianScores
