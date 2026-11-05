module

public import SHE.ScalarGaussianSemigroup
public import SHE.NativeFirstWordRepresentation
public import SHE.GaussianTaylorAverage

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.ScalarGaussianProjection
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianConvolution ScalarGaussianSemigroup SmoothCylinders
open scoped NNReal

/-- Exact scalar heat identification inside the ACTUAL finite Gaussian
backward test; no replacement Gaussian law or nonsingularity is needed. -/
theorem average {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (i : Fin n)
    (a : ℝ→ℝ) (ha : Measurable a) (m : State n) :
    gaussianAverage A (fun z=>a (z i)) m=heat (A i i).toNNReal a (m i) := by
  change (∫ y : State n,a ((m+y) i) ∂multivariateGaussian 0 A)=_
  simp only [PiLp.add_apply]
  exact NativeFirstWordRepresentation.coordinate_average hA i a ha (m i)

/-- Literal full Fréchet gradient of that backward test, in every
physical finite observation direction. This connects finite Itô's
gradient row to the scalar multipliers used in the complete-Gamma bound. -/
theorem fderiv {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (i : Fin n)
    (a : ℝ→ℝ) (ha : BoundedSmooth a) (m v : State n) :
    (fderiv ℝ (gaussianAverage A (fun z=>a (z i))) m) v=
      deriv (heat (A i i).toNNReal a) (m i)*v i := by
  have he : gaussianAverage A (fun z=>a (z i))=
      (heat (A i i).toNNReal a) ∘ (EuclideanSpace.proj i) :=
    funext (fun z=>average hA i a ha.smooth.continuous.measurable z)
  rw [he]
  have hd : HasDerivAt (heat (A i i).toNNReal a)
      (deriv (heat (A i i).toNNReal a) (m i)) (m i):=
    ((heat_boundedSmooth (A i i).toNNReal ha).smooth.differentiable (by simp)).differentiableAt.hasDerivAt
  have hf:=hd.comp_hasFDerivAt m (EuclideanSpace.proj i : State n→L[ℝ] ℝ).hasFDerivAt
  rw [hf.fderiv]
  rfl

end SHE.ScalarGaussianProjection
