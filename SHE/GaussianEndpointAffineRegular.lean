module

public import SHE.GaussianEndpointAffine
public import SHE.LocalizedItoTest

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.GaussianEndpointAffine
open MeasureTheory Set ProbabilityTheory SmoothCylinders GaussianIncrement GaussianConvolution GaussianContinuity
open GaussianTaylor GaussianTaylorAverage BackwardRegularity GaussianAffineFields
open scoped NNReal ENNReal
variable {k n : ℕ}

theorem derivative_measurable (W : CovarianceEndpoint.EndpointWindow n)
    {F : State n→ℝ} (hF : BoundedSmooth F)
    {L dL : ℝ→State k→L[ℝ]State n} {m dm : ℝ→State n}
    (hL : Continuous L) (hm : Continuous m) (hdL : Measurable dL) (hdm : Measurable dm) :
    Measurable (fun p : ℝ×State k => derivative W F L dL m dm p.1 p.2) := by
  obtain ⟨M,hM⟩ := hF.norm_bound
  obtain ⟨A,hA⟩ := hF.fderiv.norm_bound
  obtain ⟨B,hB⟩ := hF.fderiv.fderiv.norm_bound
  have hp := continuous_fst.prodMk (continuous_mean hL hm)
  have hg := (gaussian_gradient_joint_continuous W.path W.continuous_path
    (hF.smooth.of_le (by simp)) hM hA).comp hp
  have hh := (gaussian_hessian_joint_continuous W.path W.continuous_path
    (hF.smooth.of_le (by simp)) hM hA hB).comp hp
  have hd : Measurable (fun p : ℝ×State k => mean dL dm p.1 p.2) := by
    exact ((isBoundedBilinearMap_apply (𝕜 := ℝ)).continuous.measurable.comp
      ((hdL.comp measurable_fst).prodMk measurable_snd)).add (hdm.comp measurable_fst)
  have he := (isBoundedBilinearMap_apply (𝕜 := ℝ)).continuous.measurable.comp
    (hg.measurable.prodMk hd)
  apply Measurable.add _ he
  apply Measurable.const_mul
  unfold covarianceAction
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  exact ((CovarianceMatrix.covarianceDensity_measurable W.coefficient W.measurable W.observations i j).comp
    measurable_fst).mul (((hh.clm_apply continuous_const).clm_apply continuous_const).measurable)

theorem derivative_state_continuous (W : CovarianceEndpoint.EndpointWindow n)
    {F : State n→ℝ} (hF : BoundedSmooth F)
    (L dL : ℝ→State k→L[ℝ]State n) (m dm : ℝ→State n) (t : ℝ) :
    Continuous (derivative W F L dL m dm t) := by
  obtain ⟨M,hM⟩ := hF.norm_bound
  obtain ⟨A,hA⟩ := hF.fderiv.norm_bound
  obtain ⟨B,hB⟩ := hF.fderiv.fderiv.norm_bound
  have hp : Continuous (fun z : State k => (t,mean L m t z)) :=
    continuous_const.prodMk ((L t).continuous.add continuous_const)
  have hg := (gaussian_gradient_joint_continuous W.path W.continuous_path
    (hF.smooth.of_le (by simp)) hM hA).comp hp
  have hh := (gaussian_hessian_joint_continuous W.path W.continuous_path
    (hF.smooth.of_le (by simp)) hM hA hB).comp hp
  apply Continuous.add _ (hg.clm_apply ((dL t).continuous.add continuous_const))
  apply Continuous.const_mul
  unfold covarianceAction
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact continuous_const.mul ((hh.clm_apply continuous_const).clm_apply continuous_const)

/-- A genuine endpoint-integrable linear growth envelope for the
complete covariance plus moving-affine-mean derivative. -/
theorem derivative_linear_envelope (W : CovarianceEndpoint.EndpointWindow n)
    {F : State n→ℝ} (hF : BoundedSmooth F)
    (L dL : ℝ→State k→L[ℝ]State n) (m dm : ℝ→State n)
    {D : ℝ} (hD : 0≤D)
    (hdL : ∀ t∈Ioo W.left W.right,‖dL t‖≤D)
    (hdm : ∀ t∈Ioo W.left W.right,‖dm t‖≤D) :
    ∃ V : ℝ→ℝ,IntervalIntegrable V volume W.left W.right ∧
      ∀ t∈Ioo W.left W.right,0≤V t ∧ ∀ z,‖derivative W F L dL m dm t z‖≤V t*(1+‖z‖) := by
  obtain ⟨M,hM⟩:=hF.norm_bound
  obtain ⟨A,hA⟩:=hF.fderiv.norm_bound
  obtain ⟨B,hB⟩:=hF.fderiv.fderiv.norm_bound
  have hA0 : 0≤A:=(norm_nonneg _).trans (hA 0)
  have hB0 : 0≤B:=(norm_nonneg _).trans (hB 0)
  let C := fun t:ℝ=>(1/2:ℝ)*(n:ℝ)^2*B*(W.upper*(1+StoppedFourier.heatConstant*(W.right-t)^(-(1/2:ℝ))))
  have hCint : IntervalIntegrable C volume W.left W.right :=
    (CovarianceEndpoint.endpoint_majorant_integrable W.upper).const_mul _
  refine ⟨fun t=>C t+2*A*D,hCint.add intervalIntegrable_const,fun t ht=>?_⟩
  have hheat : 0≤StoppedFourier.heatConstant:=StoppedFourier.heatConstant_pos.le
  have hupper : 0≤W.upper:=W.upper_nonneg
  have hr : 0≤(W.right-t)^(-(1/2:ℝ)) := (Real.rpow_pos_of_pos (sub_pos.mpr ht.2) _).le
  have hC0 : 0≤C t := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hB0)
    (mul_nonneg hupper (add_nonneg zero_le_one (mul_nonneg hheat hr)))
  refine ⟨by positivity,fun z=>?_⟩
  have hcov : ‖GaussianItoTest.backwardDerivative W F t (mean L m t z)‖≤C t:=
    GaussianItoTest.backwardDerivative_bound W (hF.smooth.of_le (by simp)) hM hA hB hB0 ht _
  have hdir : ‖mean dL dm t z‖≤D*‖z‖+D:=
    (norm_add_le _ _).trans (add_le_add
      (((dL t).le_opNorm z).trans (mul_le_mul_of_nonneg_right (hdL t ht) (norm_nonneg _))) (hdm t ht))
  have hgrad : ‖fderiv ℝ (gaussianAverage (W.path t).val F) (mean L m t z)‖≤A:=
    gaussian_state_gradient_bound _ (hF.smooth.of_le (by simp)) hM hA _
  have hmean : ‖fderiv ℝ (gaussianAverage (W.path t).val F) (mean L m t z) (mean dL dm t z)‖≤
      A*(D*‖z‖+D):=((fderiv ℝ (gaussianAverage (W.path t).val F) (mean L m t z)).le_opNorm _).trans
        (mul_le_mul hgrad hdir (norm_nonneg _) hA0)
  change ‖GaussianItoTest.backwardDerivative W F t (mean L m t z)+
    fderiv ℝ (gaussianAverage (W.path t).val F) (mean L m t z) (mean dL dm t z)‖≤_
  exact (norm_add_le _ _).trans ((add_le_add hcov hmean).trans (by
    nlinarith [norm_nonneg z,mul_nonneg hC0 (norm_nonneg z),mul_nonneg (mul_nonneg hA0 hD) (norm_nonneg z)]))

/-- The ordinary localized finite-Itô test conditions hold for a moving
affine mean and the actual endpoint covariance, including zero final age. -/
theorem smoothTimeTest (W : CovarianceEndpoint.EndpointWindow n)
    {F : State n→ℝ} (hF : BoundedSmooth F)
    (L dL : ℝ→State k→L[ℝ]State n) (m dm : ℝ→State n)
    {K D : ℝ} (hK : 0≤K) (hLbound : ∀ t,‖L t‖≤K) (hD : 0≤D)
    (KL Km : ℝ≥0) (hLlip : LipschitzWith KL L) (hmlip : LipschitzWith Km m)
    (hdL : Measurable dL) (hdm : Measurable dm)
    (hLderiv : ∀ᵐ t:ℝ,t∈Ioo W.left W.right→HasDerivAt L (dL t) t)
    (hmderiv : ∀ᵐ t:ℝ,t∈Ioo W.left W.right→HasDerivAt m (dm t) t)
    (hdLbound : ∀ t∈Ioo W.left W.right,‖dL t‖≤D)
    (hdmbound : ∀ t∈Ioo W.left W.right,‖dm t‖≤D) :
    LocalizedItoTest.SmoothTimeTest W.left W.right (value W.path F L m) (derivative W F L dL m dm) := by
  refine ⟨continuous_value W.continuous_path hF hLlip.continuous hmlip.continuous,
    uniform_smooth W.path hF L m hK hLbound,
    time_absolutelyContinuous W hF L m KL Km hLlip hmlip,
    ae_time_derivative W hF L dL m dm hLderiv hmderiv,
    derivative_measurable W hF hLlip.continuous hmlip.continuous hdL hdm,
    derivative_state_continuous W hF L dL m dm,?_⟩
  exact derivative_linear_envelope W hF L dL m dm hD hdLbound hdmbound

end SHE.GaussianEndpointAffine
