module

public import SHE.RecursiveGaussianScores
public import SHE.GaussianProjectionInsertion
public import SHE.GaussianTriangularKernel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.ProjectedUncutWord
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion
open CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianConvolution
open SmoothCylinders GaussianCoordinates
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n N : ℕ}
variable (L : CutoffWordLevel.Level R P n)

/-- The actual newest-coordinate coefficient, lifted to a selected
original coordinate of the final observation space. -/
def leaf (k : ℕ) (p : History P (k+1)) (i : Fin N) (z : WordRecursion.State N) : ℝ :=
  (1 / 2 : ℝ) * (R.totalVariance (z i) - R.reference ((carrier L k).nodeTime p,p.2.2))

theorem tail_projection {k : ℕ} (f : Fin (n+k) → Fin N) (g : Fin (n+k+1) → Fin N)
    (htail : ∀ i, g i.succ = f i) (z : WordRecursion.State N) :
    SmoothWords.tailProjection (n+k) (projection g z) = projection f z := by
  ext i
  change z (g i.succ) = z (f i)
  rw [htail i]

/-- One literal uncut recursive step, including its original coefficient
and baseline, is the lifted final-space Gaussian Hessian insertion. -/
theorem lifted_step (k : ℕ) (p : History P (k+1))
    (f : Fin (n+k) → Fin N) (g : Fin (n+k+1) → Fin N)
    (htail : ∀ i, g i.succ = f i)
    {A : MeasurableGeneralizedInverse.Mat N} (hA : A.PosSemidef)
    (hcov : A.submatrix f f = ((carrier L k).nodeCovariance p).val)
    (d : WordRecursion.State N) (hd : projection f d = row L k p) (z : WordRecursion.State N) :
    UncutSmoothWords.test L (k+1) p (projection g z) =
      leaf L k p (g 0) z * directionalSecond
        (gaussianAverage A (fun w => UncutSmoothWords.test L k p.1 (projection f w))) z d := by
  have hh := GaussianProjectionInsertion.projected_average_insertion f hA
    (RecursiveGaussianScores.test_boundedSmooth L k p.1) z d
  rw [hcov, hd] at hh
  change leaf L k p (g 0) z * directionalSecond
    (gaussianAverage ((carrier L k).nodeCovariance p).val (UncutSmoothWords.test L k p.1))
    (SmoothWords.tailProjection (n+k) (projection g z)) (row L k p) = _
  rw [tail_projection f g htail z]
  exact congrArg (fun r => leaf L k p (g 0) z * r) hh.symm

/-- The physical recursive step is the genuine old/residual score kernel
on the final observation space. The covariance and direction equations
are exact coordinate restrictions, not an abstract word identification. -/
theorem lifted_score_step (k : ℕ) (p : History P (k+1))
    (f : Fin (n+k) → Fin N) (g : Fin (n+k+1) → Fin N)
    (htail : ∀ i, g i.succ = f i)
    {old residual : MeasurableGeneralizedInverse.Mat N}
    (ho : old.PosSemidef) (hr : residual.PosSemidef)
    (hcov : (old + residual).submatrix f f = ((carrier L k).nodeCovariance p).val)
    (d : WordRecursion.State N) (hd : projection f d = row L k p)
    (hrange : d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) old).range) (z : WordRecursion.State N) :
    UncutSmoothWords.test L (k+1) p (projection g z) =
      leaf L k p (g 0) z * (GaussianTriangularKernel.kernel old residual d).action
        (fun w => UncutSmoothWords.test L k p.1 (projection f w)) z := by
  rw [lifted_step L k p f g htail (ho.add hr) hcov d hd z]
  rw [GaussianTriangularKernel.action_eq_hessian ho hr hrange
    ((RecursiveGaussianScores.test_boundedSmooth L k p.1).comp_right (projection f)) z]

end SHE.ProjectedUncutWord
