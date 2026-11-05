module

public import SHE.TotalSmoothLimit
public import SHE.ControlledProfileFamilies

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ControlledSmoothLimit
open Set Filter MeasureTheory AddCircle StoppedFourier SmoothApproximation ScalarData
  GaussianProfile ControlledProfile TotalSmoothLimit
open scoped Topology
local instance controlledSmoothLimit_periodPos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable (D : ScalarData) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hsmall : contractionConstant D.ell D.holderConstant D.beta * h ^ (D.beta / 4) ≤ 1 / 2)

def roughTotalParameters : CanonicalCovariance.ProfileParameters :=
  TotalProfileParameters.add (D.roughProfileParameters h hh hh1 hsmall) (amplitude D)

def smoothTotalParameters (n : ℕ) : CanonicalCovariance.ProfileParameters :=
  TotalProfileParameters.add (D.smoothProfileParameters h hh hh1 hsmall n) (amplitude D)

/-- Uniform coefficient approximation for the actual damped controlled
profile, with its prescribed hybrid mean. The bound is simultaneous over
all old inputs, signed directions, damping values and interpolation
parameters, on the same fixed-point horizon. -/
theorem total_profile_error (n : ℕ) (Λ : ℝ) (u d : CircleL2) (θ : ℝ) (p : Domain) :
    |profile (smoothTotalParameters D hh hh1 hsmall n) Λ u d (θ, p) -
      profile (roughTotalParameters D hh hh1 hsmall) Λ u d (θ, p)| ≤ SmoothReferenceLimit.error D n := by
  let P := roughTotalParameters D hh hh1 hsmall
  let Q := smoothTotalParameters D hh hh1 hsmall n
  have hdiff (z : ℝ) : |Q.coefficient z - P.coefficient z| ≤
      D.holderConstant * CompactMollifier.radius n ^ D.beta := by
    change |((amplitude D) ^ 2 + D.smoothCoefficient n z) -
      ((amplitude D) ^ 2 + D.residualCoefficient z)| ≤ _
    rw [add_sub_add_left_eq_sub]
    exact CompactMollifier.approximant_error D.residual_continuous D.holderConstant_nonneg
      D.beta_pos.le D.residual_holder n z
  have he := ProfileCoefficientStability.canonical_coefficient_bound Q.measurable P.measurable
    (mean_measurable Λ u d) P.lower_pos P.upper_nonneg P.holder_nonneg
    P.exponent_pos P.exponent_le_one P.horizon_pos P.horizon_le_one
    Q.lower_bound Q.upper_bound P.lower_bound P.upper_bound Q.holder_bound P.holder_bound P.small
    (mul_nonneg D.holderConstant_nonneg (Real.rpow_nonneg (CompactMollifier.radius_pos n).le _)) hdiff (θ, p)
  exact he.trans_eq (by simp only [SmoothReferenceLimit.error, mul_assoc])

/-- Subtracting the common additive variance gives convergence of the
actual residual common-Haar reference coefficient, with the same error. -/
theorem residual_profile_error (n : ℕ) (Λ : ℝ) (u d : CircleL2) (θ : ℝ) (p : Domain) :
    |(profile (smoothTotalParameters D hh hh1 hsmall n) Λ u d (θ, p) - (amplitude D) ^ 2) -
      (profile (roughTotalParameters D hh hh1 hsmall) Λ u d (θ, p) - (amplitude D) ^ 2)| ≤
      SmoothReferenceLimit.error D n := by
  rw [sub_sub_sub_cancel_right]
  exact total_profile_error D hh hh1 hsmall n Λ u d θ p

abbrev Parameters := ℝ × ((CircleL2 × CircleL2) × (ℝ × Domain))

def totalFamily (P : CanonicalCovariance.ProfileParameters) (p : Parameters) : ℝ :=
  profile P p.1 p.2.1.1 p.2.1.2 p.2.2

theorem total_profile_uniform_limit :
    TendstoUniformly (fun n => totalFamily (smoothTotalParameters D hh hh1 hsmall n))
      (totalFamily (roughTotalParameters D hh hh1 hsmall)) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [(SmoothReferenceLimit.error_tendsto D).eventually (gt_mem_nhds hε)] with n hn p
  have hb : dist (totalFamily (roughTotalParameters D hh hh1 hsmall) p)
      (totalFamily (smoothTotalParameters D hh hh1 hsmall n) p) ≤ SmoothReferenceLimit.error D n := by
    simpa only [totalFamily, Real.dist_eq, abs_sub_comm] using
      total_profile_error D hh hh1 hsmall n p.1 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2
  exact hb.trans_lt hn

end SHE.ControlledSmoothLimit
