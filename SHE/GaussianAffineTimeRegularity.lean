module

public import SHE.GaussianAffineFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.GaussianAffineFields
open MeasureTheory Set ProbabilityTheory Filter SmoothCylinders
open GaussianIncrement GaussianConvolution GaussianContinuity GaussianTaylor GaussianTaylorAverage BackwardRegularity
open scoped NNReal ENNReal Matrix.Norms.Elementwise
variable {k n : ℕ}

/-- Absolute continuity of the actual moving-mean Gaussian reserve
follows from its ordered covariance trace and the concrete affine mean
Lipschitz bound. Singular covariance and collisions are allowed. -/
theorem time_absolutelyContinuous (W : ClippedCovariance.ObservationWindow n)
    {F : State n→ℝ} (hF : BoundedSmooth F)
    (L : ℝ→State k→L[ℝ]State n) (m : ℝ→State n)
    (KL Km : ℝ≥0) (hL : LipschitzWith KL L) (hm : LipschitzWith Km m) (z : State k) :
    AbsolutelyContinuousOnInterval (fun t => value W.path F L m t z) W.left W.right := by
  obtain ⟨M,hM⟩ := hF.norm_bound
  obtain ⟨A,hA⟩ := hF.fderiv.norm_bound
  obtain ⟨B,hB⟩ := hF.fderiv.fderiv.norm_bound
  have hA0 : 0≤A := (norm_nonneg _).trans (hA 0)
  have hB0 : 0≤B := (norm_nonneg _).trans (hB 0)
  have hz := ((ContinuousLinearMap.apply ℝ (State n) z).lipschitz.comp hL).add hm
  change LipschitzWith _ (fun t => mean L m t z) at hz
  exact (GaussianTimeLipschitz.value_lipschitz W.path (fun _ _ h => W.path_antitone h)
    _ (observation_trace_lipschitz W) (fun t => mean L m t z) _ hz
    (hF.smooth.of_le (by simp)) hM hA hB hA0 hB0).lipschitzOnWith.absolutelyContinuousOnInterval

/-- The actual joint mean/covariance chain rule, simultaneously at all
states almost everywhere in time. The covariance derivative is proved
from the original physical heat/profile integral. -/
theorem ae_time_derivative (W : ClippedCovariance.ObservationWindow n)
    {F : State n→ℝ} (hF : BoundedSmooth F)
    (L dL : ℝ→State k→L[ℝ]State n) (m dm : ℝ→State n)
    (hL : ∀ᵐ t : ℝ,t∈Ioo W.left W.right → HasDerivAt L (dL t) t)
    (hm : ∀ᵐ t : ℝ,t∈Ioo W.left W.right → HasDerivAt m (dm t) t) :
    ∀ᵐ t : ℝ,t∈Ioo W.left W.right → ∀ z,
      HasDerivAt (fun r => value W.path F L m r z) (derivative W F L dL m dm t z) t := by
  obtain ⟨M,hM⟩ := hF.norm_bound
  obtain ⟨A,hA⟩ := hF.fderiv.norm_bound
  obtain ⟨B,hB⟩ := hF.fderiv.fderiv.norm_bound
  obtain ⟨K,hK,hHK⟩ := hF.hessian_lipschitz
  have hB0 : 0≤B := (norm_nonneg _).trans (hB 0)
  filter_upwards [W.path_ae_hasDerivAt,hL,hm] with t ht hL hm htin z
  have hmean := ((ContinuousLinearMap.apply ℝ (State n) z).hasFDerivAt.comp_hasDerivAt t (hL htin)).add (hm htin)
  change HasDerivAt (fun r => mean L m r z) (mean dL dm t z) t at hmean
  have hp := GaussianCovariancePath.hasDerivAt_monotone_gaussian_average W.path (ht htin)
    (fun _ _ h => W.path_antitone h) (hF.smooth.of_le (by simp)) hM hA hB hK hHK (mean L m t z)
  have hh := GaussianMovingMean.hasDerivAt_moving_mean_of_partial W.path W.continuous_path.continuousAt
    (fun r => mean L m r z) hmean hp (hF.smooth.of_le (by simp)) hM hA hB hB0
  rw [GaussianBackward.covarianceAction_neg,mul_neg] at hh
  simpa only [value,derivative,neg_mul] using hh

end SHE.GaussianAffineFields
