module

public import SHE.GaussianAffineFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.GaussianAffineFields
open MeasureTheory Set ProbabilityTheory SmoothCylinders
open GaussianIncrement GaussianConvolution GaussianTaylor GaussianTaylorAverage BackwardRegularity
open scoped NNReal ENNReal
variable {k n : ℕ}

/-- The physical covariance density and the actual affine mean
derivative give a proved linear state-growth envelope. It retains all
mixed observation pairs and requires no inverse covariance bound. -/
theorem derivative_linear_envelope (W : ClippedCovariance.ObservationWindow n)
    {F : State n→ℝ} (hF : BoundedSmooth F)
    (L dL : ℝ→State k→L[ℝ]State n) (m dm : ℝ→State n)
    {D : ℝ} (hD : 0≤D)
    (hdL : ∀ t∈Ioo W.left W.right,‖dL t‖≤D) (hdm : ∀ t∈Ioo W.left W.right,‖dm t‖≤D) :
    ∃ V : ℝ,0≤V ∧ ∀ t∈Ioo W.left W.right,∀ z,
      ‖derivative W F L dL m dm t z‖≤V*(1+‖z‖) := by
  obtain ⟨M,hM⟩ := hF.norm_bound
  obtain ⟨A,hA⟩ := hF.fderiv.norm_bound
  obtain ⟨B,hB⟩ := hF.fderiv.fderiv.norm_bound
  have hA0 : 0≤A := (norm_nonneg _).trans (hA 0)
  have hB0 : 0≤B := (norm_nonneg _).trans (hB 0)
  let P := W.upper*(CovarianceMatrix.heatRowBound W.gap)^2
  have hP : 0≤P := mul_nonneg W.upper_nonneg (sq_nonneg _)
  let C₀ := (1/2:ℝ)*((n:ℝ)^2*P*B)
  have hC₀ : 0≤C₀ := by dsimp [C₀]; positivity
  refine ⟨C₀+2*A*D,by positivity,fun t ht z => ?_⟩
  let H := hessian (gaussianAverage (W.path t).val F) (mean L m t z)
  let Γ := CovarianceMatrix.densityMatrix W.coefficient W.observations t
  have hΓ : ∀ i j,|Γ i j|≤P := fun i j => CovarianceMatrix.covarianceDensity_bound
    W.coefficient W.measurable W.observations W.gap_pos W.upper_nonneg W.target_gap ht.2.le
    (W.bounded t (Ioo_subset_Icc_self ht)) i j
  have hH : ‖H‖≤B := gaussian_state_hessian_bound _ (hF.smooth.of_le (by simp)) hM hA hB _
  have haction : ‖covarianceAction Γ H‖≤(n:ℝ)^2*P*B :=
    (GaussianItoTest.action_entry_bound Γ H hP hΓ).trans
      (mul_le_mul_of_nonneg_left hH (mul_nonneg (sq_nonneg _) hP))
  have hcov : ‖-(1/2:ℝ)*covarianceAction Γ H‖≤C₀ := by
    calc
      _=(1/2:ℝ)*‖covarianceAction Γ H‖ := by rw [norm_mul]; norm_num
      _≤_ := mul_le_mul_of_nonneg_left haction (by norm_num)
  have hdir : ‖mean dL dm t z‖≤D*‖z‖+D :=
    (norm_add_le _ _).trans (add_le_add
      (((dL t).le_opNorm z).trans (mul_le_mul_of_nonneg_right (hdL t ht) (norm_nonneg _))) (hdm t ht))
  have hgrad : ‖fderiv ℝ (gaussianAverage (W.path t).val F) (mean L m t z)‖≤A :=
    gaussian_state_gradient_bound _ (hF.smooth.of_le (by simp)) hM hA _
  have hmean : ‖fderiv ℝ (gaussianAverage (W.path t).val F) (mean L m t z) (mean dL dm t z)‖≤
      A*(D*‖z‖+D) := ((fderiv ℝ (gaussianAverage (W.path t).val F) (mean L m t z)).le_opNorm _).trans
    (mul_le_mul hgrad hdir (norm_nonneg _) hA0)
  calc
    _≤‖-(1/2:ℝ)*covarianceAction Γ H‖+
      ‖fderiv ℝ (gaussianAverage (W.path t).val F) (mean L m t z) (mean dL dm t z)‖ := norm_add_le _ _
    _≤C₀+A*(D*‖z‖+D) := add_le_add hcov hmean
    _≤_ := by
      nlinarith [norm_nonneg z,mul_nonneg hC₀ (norm_nonneg z),
        mul_nonneg (mul_nonneg hA0 hD) (norm_nonneg z)]

end SHE.GaussianAffineFields
