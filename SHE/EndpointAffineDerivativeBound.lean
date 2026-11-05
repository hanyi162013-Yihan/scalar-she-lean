module

public import SHE.GaussianEndpointAffineRegular

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.EndpointAffineDerivativeBound
open Set MeasureTheory GaussianIncrement SmoothCylinders GaussianTaylor GaussianTaylorAverage
open GaussianAffineFields GaussianConvolution
variable {k n : ℕ}

/-- An explicit scalar envelope for the actual affine Gaussian time
chain. The constants do not involve the affine center or a past state. -/
theorem bound (W : CovarianceEndpoint.EndpointWindow n) {F : State n→ℝ} (hF : BoundedSmooth F)
    {A B M D : ℝ} (hA0 : 0≤A) (hB0 : 0≤B) (hD0 : 0≤D)
    (hM : ∀ z,‖F z‖≤M) (hA : ∀ z,‖fderiv ℝ F z‖≤A) (hB : ∀ z,‖hessian F z‖≤B)
    (L DL : ℝ→State k→L[ℝ]State n) {t : ℝ} (ht : t∈Ioo W.left W.right)
    (hDL : ‖DL t‖≤D) (z : State k) :
    ‖GaussianEndpointAffine.derivative W F L DL (fun _=>0) (fun _=>0) t z‖≤
      ((1/2:ℝ)*(n:ℝ)^2*B*(W.upper*(1+StoppedFourier.heatConstant*(W.right-t)^(-(1/2:ℝ))))+A*D)*(1+‖z‖) := by
  let C:=(1/2:ℝ)*(n:ℝ)^2*B*(W.upper*(1+StoppedFourier.heatConstant*(W.right-t)^(-(1/2:ℝ))))
  have hC0 : 0≤C:=mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hB0)
    (mul_nonneg W.upper_nonneg (add_nonneg zero_le_one
      (mul_nonneg StoppedFourier.heatConstant_pos.le (Real.rpow_nonneg (sub_pos.mpr ht.2).le _))))
  have hc : ‖GaussianItoTest.backwardDerivative W F t (L t z)‖≤C:=
    GaussianItoTest.backwardDerivative_bound W (hF.smooth.of_le (by simp)) hM hA hB hB0 ht _
  have hg : ‖fderiv ℝ (gaussianAverage (W.path t).val F) (L t z)‖≤A:=
    BackwardRegularity.gaussian_state_gradient_bound _ (hF.smooth.of_le (by simp)) hM hA _
  have hd : ‖DL t z‖≤D*‖z‖:=((DL t).le_opNorm z).trans
    (mul_le_mul_of_nonneg_right hDL (norm_nonneg _))
  have hm : ‖fderiv ℝ (gaussianAverage (W.path t).val F) (L t z) (DL t z)‖≤A*(D*‖z‖):=
    ((fderiv ℝ (gaussianAverage (W.path t).val F) (L t z)).le_opNorm _).trans
      (mul_le_mul hg hd (norm_nonneg _) hA0)
  simp only [GaussianEndpointAffine.derivative,mean,add_zero]
  change ‖GaussianItoTest.backwardDerivative W F t (L t z)+
    fderiv ℝ (gaussianAverage (W.path t).val F) (L t z) (DL t z)‖≤_
  exact (norm_add_le _ _).trans ((add_le_add hc hm).trans (by
    change C+A*(D*‖z‖)≤(C+A*D)*(1+‖z‖)
    nlinarith [norm_nonneg z,mul_nonneg hC0 (norm_nonneg z),mul_nonneg hA0 hD0]))

end SHE.EndpointAffineDerivativeBound
