module

public import SHE.GaussianCoordinates
public import SHE.GaussianFixedScore

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.GaussianProjectionInsertion
open Set MeasureTheory ProbabilityTheory WordRecursion SmoothCylinders GaussianConvolution
open scoped ContDiff
variable {n m : ℕ}

/-- Hessian insertions commute with the genuine linear projection from
the final observation space to the current word's original coordinates. -/
theorem directionalSecond_comp (L : State n →L[ℝ] State m)
    {F : State m → ℝ} (hF : BoundedSmooth F) (z d : State n) :
    directionalSecond (fun x => F (L x)) z d = directionalSecond F (L z) (L d) := by
  have h := congrArg (fun T => T (fun _ : Fin 2 => d))
    (L.iteratedFDeriv_comp_right hF.smooth z (by simp : (2 : WithTop ℕ∞) ≤ ∞))
  simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_two_apply, directionalSecond, hessian, Function.comp_def] using h

/-- The actual covariance average followed by a physical Hessian
insertion can be lifted to the final coordinate space before introducing
the old score. -/
theorem projected_average_insertion (f : Fin m → Fin n)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    {F : State m → ℝ} (hF : BoundedSmooth F) (z d : State n) :
    directionalSecond (gaussianAverage A (fun x => F (GaussianCoordinates.projection f x))) z d =
      directionalSecond (gaussianAverage (A.submatrix f f) F)
        (GaussianCoordinates.projection f z) (GaussianCoordinates.projection f d) := by
  have he : gaussianAverage A (fun x => F (GaussianCoordinates.projection f x)) =
      fun z => gaussianAverage (A.submatrix f f) F (GaussianCoordinates.projection f z) := by
    funext w
    exact GaussianCoordinates.average_projection f hA F hF.smooth.continuous.measurable w
  rw [he]
  exact directionalSecond_comp (GaussianCoordinates.projection f)
    (hF.average (multivariateGaussian (0 : State m) (A.submatrix f f))) z d

end SHE.GaussianProjectionInsertion
