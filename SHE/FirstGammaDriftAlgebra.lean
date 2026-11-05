module

public import SHE.FiniteAffineDriftCancellation
public import SHE.FirstGammaTestFields

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.FirstGammaDriftAlgebra
open GaussianIncrement GaussianTaylor GaussianTaylorAverage GaussianConvolution SmoothCylinders
open FiniteCovariancePullback
variable {n : ℕ} {C : Type*} [NormedAddCommGroup C] [InnerProductSpace ℝ C]

/-- The exact finite-dimensional Gaussian drift cancellation for the
corrected current/reference test. All cross rows are retained. -/
theorem cancellation (W : CovarianceEndpoint.EndpointWindow n) {F : State n→ℝ}
    (hF : BoundedSmooth F) (Λ θ : ℝ) (target : Fin n→ℝ) (t : ℝ)
    (R : Fin ((n+n)+(n+n))→C) (z : FirstGammaAffine.Space n)
    (href : gram (mappedRow (FirstGammaAffine.reference n Λ θ target) R)=
      CovarianceMatrix.densityMatrix W.coefficient W.observations t) :
    FirstGammaGaussianTest.testDerivative W F Λ θ target t z+
      (1/2:ℝ)*covarianceAction (gram R)
        (hessian (FirstGammaGaussianTest.test W F Λ θ target t) z)=
    fderiv ℝ (gaussianAverage (W.path t).val F)
        (FirstGammaAffine.current n Λ θ target t z)
        (FirstGammaAffine.currentDerivative n Λ θ t z)+
      (1/2:ℝ)*covarianceAction
        (gram (mappedRow (FirstGammaAffine.current n Λ θ target t) R)-
          CovarianceMatrix.densityMatrix W.coefficient W.observations t)
        (hessian (gaussianAverage (W.path t).val F)
          (FirstGammaAffine.current n Λ θ target t z)) := by
  have hs : BoundedSmooth (gaussianAverage (W.path t).val F) :=
    hF.average (ProbabilityTheory.multivariateGaussian (0:State n) (W.path t).val)
  have hh:=FiniteAffineDriftCancellation.cancellation
    (CovarianceMatrix.densityMatrix W.coefficient W.observations t)
    (FirstGammaAffine.current n Λ θ target t)
    (FirstGammaAffine.reference n Λ θ target)
    (FirstGammaAffine.currentDerivative n Λ θ t) R hs z href
  have he : FirstGammaGaussianTest.test W F Λ θ target t=
      (fun w=>gaussianAverage (W.path t).val F (FirstGammaAffine.current n Λ θ target t w)-
        gaussianAverage (W.path t).val F (FirstGammaAffine.reference n Λ θ target w)) := by
    funext w
    simp only [FirstGammaGaussianTest.test,FirstGammaGaussianTest.currentValue,
      FirstGammaGaussianTest.referenceValue,GaussianAffineFields.value,
      GaussianAffineFields.mean,add_zero]
  rw [he]
  simpa only [FirstGammaGaussianTest.testDerivative,FirstGammaGaussianTest.currentDerivative,
    FirstGammaGaussianTest.referenceDerivative,GaussianEndpointAffine.derivative,
    GaussianAffineFields.mean,add_zero,ContinuousLinearMap.zero_apply,map_zero,add_zero,sub_zero] using hh

end SHE.FirstGammaDriftAlgebra
