module

public import SHE.GaussianAffineFields
public import SHE.GaussianMovingAbsoluteContinuity

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.GaussianEndpointAffine
open Set MeasureTheory ProbabilityTheory Filter SmoothCylinders GaussianIncrement GaussianConvolution GaussianContinuity
open GaussianTaylor GaussianTaylorAverage BackwardRegularity
open scoped NNReal ENNReal Matrix.Norms.Elementwise
variable {k n : ℕ}

def derivative (W : CovarianceEndpoint.EndpointWindow n) (F : State n→ℝ)
    (L dL : ℝ→State k→L[ℝ]State n) (m dm : ℝ→State n) (t : ℝ) (z : State k) : ℝ :=
  -(1/2:ℝ)*covarianceAction (CovarianceMatrix.densityMatrix W.coefficient W.observations t)
    (hessian (gaussianAverage (W.path t).val F) (GaussianAffineFields.mean L m t z))+
      fderiv ℝ (gaussianAverage (W.path t).val F) (GaussianAffineFields.mean L m t z)
        (GaussianAffineFields.mean dL dm t z)

/-- Moving affine means preserve absolute continuity of the actual
Gaussian reserve THROUGH a terminal heat singularity. -/
theorem time_absolutelyContinuous (W : CovarianceEndpoint.EndpointWindow n)
    {F : State n→ℝ} (hF : BoundedSmooth F)
    (L : ℝ→State k→L[ℝ]State n) (m : ℝ→State n)
    (KL Km : ℝ≥0) (hL : LipschitzWith KL L) (hm : LipschitzWith Km m) (z : State k) :
    AbsolutelyContinuousOnInterval (fun t=>GaussianAffineFields.value W.path F L m t z) W.left W.right := by
  obtain ⟨M,hM⟩:=hF.norm_bound
  obtain ⟨A,hA⟩:=hF.fderiv.norm_bound
  obtain ⟨B,hB⟩:=hF.fderiv.fderiv.norm_bound
  have hA0 : 0≤A:=(norm_nonneg _).trans (hA 0)
  have hB0 : 0≤B:=(norm_nonneg _).trans (hB 0)
  have hz:=((ContinuousLinearMap.apply ℝ (State n) z).lipschitz.comp hL).add hm
  exact GaussianMovingAbsoluteContinuity.average W.path (fun _ _ h=>W.path_antitone h)
    W.path_trace_absolutelyContinuous (fun t=>GaussianAffineFields.mean L m t z) _ hz
    (hF.smooth.of_le (by simp)) hM hA hB hA0 hB0

/-- The joint covariance/mean chain rule for the actual endpoint
window, with the original physical covariance derivative. -/
theorem ae_time_derivative (W : CovarianceEndpoint.EndpointWindow n)
    {F : State n→ℝ} (hF : BoundedSmooth F)
    (L dL : ℝ→State k→L[ℝ]State n) (m dm : ℝ→State n)
    (hL : ∀ᵐ t:ℝ,t∈Ioo W.left W.right→HasDerivAt L (dL t) t)
    (hm : ∀ᵐ t:ℝ,t∈Ioo W.left W.right→HasDerivAt m (dm t) t) :
    ∀ᵐ t:ℝ,t∈Ioo W.left W.right→∀ z,
      HasDerivAt (fun r=>GaussianAffineFields.value W.path F L m r z) (derivative W F L dL m dm t z) t := by
  obtain ⟨M,hM⟩:=hF.norm_bound
  obtain ⟨A,hA⟩:=hF.fderiv.norm_bound
  obtain ⟨B,hB⟩:=hF.fderiv.fderiv.norm_bound
  obtain ⟨K,hK,hHK⟩:=hF.hessian_lipschitz
  have hB0 : 0≤B:=(norm_nonneg _).trans (hB 0)
  filter_upwards [W.path_ae_hasDerivAt,hL,hm] with t ht hLt hmt htin z
  have hmean:=((ContinuousLinearMap.apply ℝ (State n) z).hasFDerivAt.comp_hasDerivAt t (hLt htin)).add (hmt htin)
  change HasDerivAt (fun r=>GaussianAffineFields.mean L m r z) (GaussianAffineFields.mean dL dm t z) t at hmean
  have hp:=GaussianCovariancePath.hasDerivAt_monotone_gaussian_average W.path (ht htin)
    (fun _ _ h=>W.path_antitone h) (hF.smooth.of_le (by simp)) hM hA hB hK hHK (GaussianAffineFields.mean L m t z)
  have hh:=GaussianMovingMean.hasDerivAt_moving_mean_of_partial W.path W.continuous_path.continuousAt
    (fun r=>GaussianAffineFields.mean L m r z) hmean hp (hF.smooth.of_le (by simp)) hM hA hB hB0
  rw [GaussianBackward.covarianceAction_neg,mul_neg] at hh
  simpa only [GaussianAffineFields.value,derivative,neg_mul] using hh

end SHE.GaussianEndpointAffine
