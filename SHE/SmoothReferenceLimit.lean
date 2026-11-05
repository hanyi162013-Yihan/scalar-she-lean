module

public import SHE.ProfileCoefficientStability

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.SmoothReferenceLimit
open MeasureTheory ProbabilityTheory SmoothApproximation ScalarData CanonicalProfile StoppedFourier
open scoped Topology
variable (D : ScalarData) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hsmall : GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*h^(D.beta/4) ≤ 1/2)

def error (n : ℕ) : ℝ := 2*D.holderConstant*CompactMollifier.radius n^D.beta

theorem error_nonneg (n : ℕ) : 0 ≤ error D n :=
  mul_nonneg (mul_nonneg (by norm_num) D.holderConstant_nonneg) (Real.rpow_nonneg (CompactMollifier.radius_pos n).le _)

theorem error_tendsto : Filter.Tendsto (error D) Filter.atTop (𝓝 (0:ℝ)) := by
  change Filter.Tendsto (fun n => 2*D.holderConstant*CompactMollifier.radius n^D.beta) Filter.atTop (𝓝 (0:ℝ))
  simpa only [Real.zero_rpow D.beta_pos.ne',mul_zero] using
    (CompactMollifier.radius_tendsto.rpow_const (Or.inr D.beta_pos.le)).const_mul (2*D.holderConstant)

variable [MeasurableSpace CircleL2] [BorelSpace CircleL2]
include hh hh1 hsmall

/-- The genuine canonical Gaussian profiles of the smooth residual
coefficients converge with a bound uniform over ALL initial L² states. -/
theorem profile_error (n : ℕ) (p : CircleL2 × ParametricProfile.Domain) :
    |profile (D.smoothCoefficient n) D.ell h p-profile D.residualCoefficient D.ell h p| ≤ error D n := by
  have he := ProfileCoefficientStability.canonical_coefficient_bound
    (D.smooth_boundedSmooth n).smooth.continuous.measurable D.residual_continuous.measurable
    PhysicalProfile.physicalHeatMean_joint_measurable D.ell_pos D.cap_nonneg D.holderConstant_nonneg
    D.beta_pos D.beta_le_one hh hh1 (fun z => (D.smooth_bounds n z).1)
    (fun z => (D.smooth_bounds n z).2) (fun z => (D.residual_bounds z).1)
    (fun z => (D.residual_bounds z).2) (D.smooth_holder n) D.residual_holder hsmall
    (mul_nonneg D.holderConstant_nonneg (Real.rpow_nonneg (CompactMollifier.radius_pos n).le _))
    (CompactMollifier.approximant_error D.residual_continuous D.holderConstant_nonneg
      D.beta_pos.le D.residual_holder n) p
  simpa only [profile,error,mul_assoc] using he

theorem profile_tendstoUniformly :
    TendstoUniformly (fun n => profile (D.smoothCoefficient n) D.ell h)
      (profile D.residualCoefficient D.ell h) Filter.atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [(error_tendsto D).eventually (gt_mem_nhds hε)] with n hn p
  have hb : dist (profile D.residualCoefficient D.ell h p) (profile (D.smoothCoefficient n) D.ell h p) ≤ error D n := by
    simpa only [Real.dist_eq,abs_sub_comm] using profile_error D hh hh1 hsmall n p
  exact hb.trans_lt hn

end SHE.SmoothReferenceLimit
