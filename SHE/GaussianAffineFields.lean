module

public import SHE.UniformAffineSmooth
public import SHE.GaussianTimeLipschitz
public import SHE.GaussianItoTest

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
noncomputable section

namespace SHE.GaussianAffineFields
open MeasureTheory Set ProbabilityTheory UniformSmooth SmoothCylinders
open GaussianIncrement GaussianConvolution GaussianContinuity GaussianTaylor GaussianTaylorAverage BackwardRegularity
open scoped NNReal ENNReal
variable {k n : ℕ}

def mean (L : ℝ→State k→L[ℝ]State n) (m : ℝ→State n) (t : ℝ) (z : State k) : State n := L t z+m t

def value (C : ℝ→PositiveCovariance n) (F : State n→ℝ)
    (L : ℝ→State k→L[ℝ]State n) (m : ℝ→State n) (t : ℝ) (z : State k) : ℝ :=
  gaussianAverage (C t).val F (mean L m t z)

theorem continuous_mean {L : ℝ→State k→L[ℝ]State n} {m : ℝ→State n}
    (hL : Continuous L) (hm : Continuous m) : Continuous (fun p : ℝ×State k => mean L m p.1 p.2) :=
  ((hL.comp continuous_fst).clm_apply continuous_snd).add (hm.comp continuous_fst)

theorem uniform_smooth (C : ℝ→PositiveCovariance n) {F : State n→ℝ} (hF : BoundedSmooth F)
    (L : ℝ→State k→L[ℝ]State n) (m : ℝ→State n) {K : ℝ} (hK : 0≤K) (hL : ∀ t,‖L t‖≤K) :
    UniformBoundedSmooth (value C F L m) := by
  have hg : UniformBoundedSmooth (fun t => gaussianAverage (C t).val F) :=
    (UniformBoundedSmooth.fixed (P := ℝ) hF).average
      (fun t => multivariateGaussian 0 (C t).val) (fun _ => inferInstance)
  exact UniformAffineSmooth.comp_affine hg L m hK hL

theorem continuous_value {C : ℝ→PositiveCovariance n} (hC : Continuous C)
    {F : State n→ℝ} (hF : BoundedSmooth F)
    {L : ℝ→State k→L[ℝ]State n} {m : ℝ→State n} (hL : Continuous L) (hm : Continuous m) :
    Continuous (fun p : ℝ×State k => value C F L m p.1 p.2) := by
  obtain ⟨M,hM⟩ := hF.norm_bound
  have hc := continuous_gaussian_average (n := n) F hF.smooth.continuous hM
  have hp : Continuous (fun p : ℝ×State k => (C p.1,mean L m p.1 p.2)) :=
    (hC.comp continuous_fst).prodMk (continuous_mean hL hm)
  have hh := hc.comp hp
  exact hh

def derivative (W : ClippedCovariance.ObservationWindow n) (F : State n→ℝ)
    (L dL : ℝ→State k→L[ℝ]State n) (m dm : ℝ→State n) (t : ℝ) (z : State k) : ℝ :=
  -(1/2:ℝ)*covarianceAction (CovarianceMatrix.densityMatrix W.coefficient W.observations t)
    (hessian (gaussianAverage (W.path t).val F) (mean L m t z))+
      fderiv ℝ (gaussianAverage (W.path t).val F) (mean L m t z) (mean dL dm t z)

theorem derivative_measurable (W : ClippedCovariance.ObservationWindow n)
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

theorem derivative_state_continuous (W : ClippedCovariance.ObservationWindow n)
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

end SHE.GaussianAffineFields
