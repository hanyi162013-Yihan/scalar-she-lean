module

public import SHE.GaussianEndpointAffineRegular
public import SHE.DampedAffineGaussian

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SHE.DampedEndpointAffine
open Set MeasureTheory GaussianIncrement SmoothCylinders
open scoped NNReal ENNReal
variable {k n : ℕ}

/-- Genuine endpoint Gaussian regularity for the exponentially varying
finite affine mean. The final Gaussian reserve may be zero. -/
theorem smoothTimeTest (W : CovarianceEndpoint.EndpointWindow n) (hleft : 0≤W.left)
    {F : State n→ℝ} (hF : BoundedSmooth F) {Λ : ℝ} (hΛ : 0≤Λ) (θ : ℝ)
    (P Q : State k→L[ℝ]State n) (d e : State n) :
    LocalizedItoTest.SmoothTimeTest W.left W.right
      (GaussianAffineFields.value W.path F (DampedAffineGaussian.linear Λ θ P Q)
        (DampedAffineGaussian.shift Λ θ d e))
      (GaussianEndpointAffine.derivative W F (DampedAffineGaussian.linear Λ θ P Q)
        (DampedAffineGaussian.linearDerivative Λ θ Q)
        (DampedAffineGaussian.shift Λ θ d e) (DampedAffineGaussian.shiftDerivative Λ θ d)) := by
  obtain ⟨KL,hL⟩:=DampedAffineGaussian.lipschitz_linear hΛ θ P Q
  obtain ⟨Km,hm⟩:=DampedAffineGaussian.lipschitz_shift hΛ θ d e
  apply GaussianEndpointAffine.smoothTimeTest W hF _ _ _ _
    (by positivity : 0≤‖P‖+|θ| *‖Q‖) (DampedAffineGaussian.linear_bound hΛ θ P Q)
    (by positivity : 0≤Λ*|θ| *(‖Q‖+‖d‖)) KL Km hL hm
  · exact ((continuous_const.mul (ClippedExponential.continuous_coefficient Λ θ)).smul continuous_const).measurable
  · exact (((continuous_const.mul (ClippedExponential.continuous_coefficient Λ θ)).smul continuous_const).neg).measurable
  · exact Filter.Eventually.of_forall (fun t ht=>DampedAffineGaussian.hasDerivAt_linear P Q (hleft.trans_lt ht.1))
  · exact Filter.Eventually.of_forall (fun t ht=>DampedAffineGaussian.hasDerivAt_shift d e (hleft.trans_lt ht.1))
  · exact fun t _=>(DampedAffineGaussian.derivative_bound hΛ θ P Q d t).1
  · exact fun t _=>(DampedAffineGaussian.derivative_bound hΛ θ P Q d t).2

end SHE.DampedEndpointAffine
