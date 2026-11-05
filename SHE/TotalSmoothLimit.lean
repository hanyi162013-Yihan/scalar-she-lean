module

public import SHE.AdditiveReference

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.TotalSmoothLimit
open MeasureTheory ProbabilityTheory Set StoppedFourier CanonicalProfile AdditiveProfile
open SmoothApproximation ScalarData GaussianProfile
open scoped Topology

variable (D : ScalarData) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hsmall : contractionConstant D.ell D.holderConstant D.beta*h^(D.beta/4) ≤ 1/2)

def roughParameters : CanonicalCovariance.ProfileParameters := D.roughProfileParameters h hh hh1 hsmall
def smoothParameters (n : ℕ) : CanonicalCovariance.ProfileParameters := D.smoothProfileParameters h hh hh1 hsmall n
def amplitude : ℝ := ScalarReduction.additiveAmplitude D.lower

theorem total_original (z : ℝ) : totalCoefficient (amplitude D) D.residualCoefficient z=(D.coefficient z)^2 :=
  D.variance_split z

variable [MeasurableSpace CircleL2] [BorelSpace CircleL2]
include hh hh1 hsmall

/-- Genuine total-variance canonical profiles, and their residual
common-Haar coefficients, share a modulus uniform over all initial states. -/
theorem residual_profile_error (n : ℕ) (p : CircleL2 × ParametricProfile.Domain) :
    |residualProfile (amplitude D) (D.smoothCoefficient n) D.ell h p-
      residualProfile (amplitude D) D.residualCoefficient D.ell h p| ≤ SmoothReferenceLimit.error D n := by
  let P := TotalProfileParameters.add (roughParameters D hh hh1 hsmall) (amplitude D)
  let Q := TotalProfileParameters.add (smoothParameters D hh hh1 hsmall n) (amplitude D)
  have hdiff (z : ℝ) : |Q.coefficient z-P.coefficient z| ≤ D.holderConstant*CompactMollifier.radius n^D.beta := by
    change |((amplitude D)^2+D.smoothCoefficient n z)-((amplitude D)^2+D.residualCoefficient z)| ≤ _
    rw [add_sub_add_left_eq_sub]
    exact CompactMollifier.approximant_error D.residual_continuous D.holderConstant_nonneg
      D.beta_pos.le D.residual_holder n z
  have he := ProfileCoefficientStability.canonical_coefficient_bound Q.measurable P.measurable
    PhysicalProfile.physicalHeatMean_joint_measurable P.lower_pos P.upper_nonneg P.holder_nonneg
    P.exponent_pos P.exponent_le_one P.horizon_pos P.horizon_le_one Q.lower_bound Q.upper_bound
    P.lower_bound P.upper_bound Q.holder_bound P.holder_bound P.small
    (mul_nonneg D.holderConstant_nonneg (Real.rpow_nonneg (CompactMollifier.radius_pos n).le _)) hdiff p
  change |(profile Q.coefficient P.lower P.horizon p-(amplitude D)^2)-
    (profile P.coefficient P.lower P.horizon p-(amplitude D)^2)| ≤ _
  rw [sub_sub_sub_cancel_right]
  simpa only [profile,SmoothReferenceLimit.error,mul_assoc] using he

theorem residual_profile_uniform_limit :
    TendstoUniformly (fun n => residualProfile (amplitude D) (D.smoothCoefficient n) D.ell h)
      (residualProfile (amplitude D) D.residualCoefficient D.ell h) Filter.atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [(SmoothReferenceLimit.error_tendsto D).eventually (gt_mem_nhds hε)] with n hn p
  have hb : dist (residualProfile (amplitude D) D.residualCoefficient D.ell h p)
      (residualProfile (amplitude D) (D.smoothCoefficient n) D.ell h p) ≤ SmoothReferenceLimit.error D n := by
    simpa only [Real.dist_eq,abs_sub_comm] using residual_profile_error D hh hh1 hsmall n p
  exact hb.trans_lt hn

end SHE.TotalSmoothLimit
