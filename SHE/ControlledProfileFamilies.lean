module

public import SHE.ControlledProfileParameter

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

/-! Jointly measurable controlled profiles and their true parameter
derivatives for measurable random input states. Exact substitution follows
from the actual Picard iterates, not a measurable selection assumption. -/
namespace SHE.ControlledProfile
open Set MeasureTheory AddCircle StoppedFourier ProfileVariance PhysicalProfile
  GaussianProfile ProfileStability ProfilePointwise ProfileParameter
open scoped NNReal Topology
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

abbrev Inputs := CircleL2 × CircleL2

def meanFamily (Λ : ℝ) (p : (Inputs × ℝ) × Domain) : ℝ :=
  mean Λ p.1.1.1 p.1.1.2 (p.1.2, p.2)

variable [MeasurableSpace CircleL2] [BorelSpace CircleL2]

theorem meanFamily_measurable (Λ : ℝ) : Measurable (meanFamily Λ) := by
  have hu : Measurable (fun p : (Inputs × ℝ) × Domain => physicalHeatMean p.1.1.1 p.2) :=
    physicalHeatMean_joint_measurable.comp
    (measurable_fst.fst.fst.prodMk measurable_snd)
  have hd : Measurable (fun p : (Inputs × ℝ) × Domain => physicalHeatMean p.1.1.2 p.2) :=
    physicalHeatMean_joint_measurable.comp
    (measurable_fst.fst.snd.prodMk measurable_snd)
  exact hu.add ((measurable_fst.snd.mul
    ((measurable_const.mul measurable_snd.fst).exp)).mul hd)

variable (P : CanonicalCovariance.ProfileParameters)

omit [MeasurableSpace CircleL2] [BorelSpace CircleL2] in
theorem profile_eq_joint (Λ : ℝ) (u d : CircleL2) (θ : ℝ) (p : Domain) :
    profile P Λ u d (θ, p) =
      ParametricProfile.canonicalProfile P.coefficient (meanFamily Λ) P.lower P.horizon (((u, d), θ), p) := by
  convert! ParametricProfile.canonicalProfile_comap P.coefficient (meanFamily Λ) P.lower P.horizon
    (fun η : ℝ => ((u, d), η)) (θ, p) using 1

theorem profile_joint_measurable (Λ : ℝ) :
    Measurable (fun p : (Inputs × ℝ) × Domain => profile P Λ p.1.1.1 p.1.1.2 (p.1.2, p.2)) := by
  have h := ParametricProfile.canonicalProfile_measurable P.measurable (meanFamily_measurable Λ)
    P.lower_pos P.upper_nonneg P.holder_nonneg P.exponent_pos P.exponent_le_one
    P.horizon_pos P.horizon_le_one P.lower_bound P.upper_bound P.holder_bound P.small
  convert! h using 1
  funext p
  exact profile_eq_joint P Λ p.1.1.1 p.1.1.2 p.1.2 p.2

theorem derivative_joint_measurable {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent *
      ProfileVolterra.powerConstant ((P.exponent - 2) / 4) * P.horizon ^ (P.exponent / 4) ≤ 1 / 2) :
    Measurable (fun p : (Inputs × Domain) × ℝ => derivative P Λ p.1.1.1 p.1.1.2 (p.1.2, p.2)) := by
  have hmap : Measurable (fun p : (Inputs × Domain) × ℝ => ((p.1.1, p.2), p.1.2)) :=
    (measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd
  have hm : Measurable (fun p : (Inputs × Domain) × ℝ =>
      profile P Λ p.1.1.1 p.1.1.2 (p.2, p.1.2)) := by
    convert! (profile_joint_measurable P Λ).comp hmap using 1
  convert! MeasuredRealCurves.derivative_measurable
    (fun p : Inputs × Domain =>
      (profile_curve_lipschitz P hΛ p.1.1 p.1.2 hsmallPoint p.2).continuous) hm using 1

theorem random_profile_measurable {X : Type*} [MeasurableSpace X] {u d : X → CircleL2}
    (hu : Measurable u) (hd : Measurable d) (Λ : ℝ) :
    Measurable (fun p : (X × ℝ) × Domain => profile P Λ (u p.1.1) (d p.1.1) (p.1.2, p.2)) := by
  convert! (profile_joint_measurable P Λ).comp
    ((((hu.prodMk hd).comp measurable_fst.fst).prodMk measurable_fst.snd).prodMk measurable_snd) using 1

omit [MeasurableSpace CircleL2] [BorelSpace CircleL2] in
theorem profile_displacement (Λ : ℝ) (u d : CircleL2) (θ : ℝ) {r : ℝ}
    (hr : r ∈ Ioc 0 P.horizon) (x : HeatCircle) :
    |profile P Λ u d (θ, (r, x)) - P.coefficient (mean Λ u d (θ, (r, x)))| ≤
      P.holder * GaussianAudit.gaussianAbsMoment P.exponent *
        (upperConstant * P.upper) ^ (P.exponent / 2) * r ^ (P.exponent / 4) := by
  have hc : Measurable (fun p => profile P Λ u d (θ, p)) :=
    (profile_measurable P Λ u d).comp (measurable_const.prodMk measurable_id)
  convert! ScalarProfileFixedPoint.scalar_profile_displacement P.measurable hc
    P.lower_pos P.upper_nonneg P.holder_nonneg P.exponent_pos.le P.horizon_le_one
    P.lower_bound P.upper_bound P.holder_bound (fun p => profile_bounds P Λ u d (θ, p))
    (fun r hr x => profile_fixed P Λ u d θ hr x) r hr x using 1

end SHE.ControlledProfile
