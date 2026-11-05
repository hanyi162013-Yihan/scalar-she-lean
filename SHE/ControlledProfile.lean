module

public import SHE.ParametricProfile
public import SHE.CanonicalCovariance
public import SHE.ProfilePointwise

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

/-! The actual canonical scalar profile for the prescribed controlled mean
S_t u + theta exp(-Lambda t) S_t d. This is a separate fixed-point object
from the profile along initial data u+theta*d. Its existence, ellipticity,
measurability and stability are derived from the genuine Gaussian update. -/
namespace SHE.ControlledProfile
open Set MeasureTheory AddCircle StoppedFourier ProfileVariance PhysicalProfile
  GaussianProfile ProfileStability ProfilePointwise ProfileL2
open scoped Topology
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

abbrev Domain := ℝ × HeatCircle

def mean (Λ : ℝ) (u d : CircleL2) (p : ℝ × Domain) : ℝ :=
  physicalHeatMean u p.2 + p.1 * Real.exp (-Λ * p.2.1) * physicalHeatMean d p.2

theorem mean_measurable (Λ : ℝ) (u d : CircleL2) : Measurable (mean Λ u d) :=
  ((physicalHeatMean_measurable u).comp measurable_snd).add
    ((measurable_fst.mul ((measurable_const.mul measurable_snd.fst).exp)).mul
      ((physicalHeatMean_measurable d).comp measurable_snd))

theorem mean_difference (Λ : ℝ) (u d : CircleL2) (θ η : ℝ) (p : Domain) :
    mean Λ u d (θ, p) - mean Λ u d (η, p) =
      ((θ - η) * Real.exp (-Λ * p.1)) * physicalHeatMean d p := by
  unfold mean
  ring

theorem damping_le_one {Λ r : ℝ} (hΛ : 0 ≤ Λ) (hr : 0 ≤ r) : Real.exp (-Λ * r) ≤ 1 :=
  Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hΛ) hr)

theorem mean_l2_difference {Λ : ℝ} (hΛ : 0 ≤ Λ) (u d : CircleL2) (θ η : ℝ)
    {r : ℝ} (hr : 0 < r) :
    MemLp (fun x => mean Λ u d (θ, (r, x)) - mean Λ u d (η, (r, x))) 2 haarAddCircle ∧
      normTwo haarAddCircle (fun x => mean Λ u d (θ, (r, x)) - mean Λ u d (η, (r, x))) ≤
        |θ - η| * ‖d‖ := by
  simp_rw [mean_difference]
  have hf := physicalHeatMean_memLp hr d
  refine ⟨hf.const_mul _, ?_⟩
  rw [normTwo_const_mul hf, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (|θ - η| * Real.exp (-Λ * r)) * ‖d‖ :=
      mul_le_mul_of_nonneg_left (physicalHeatMean_contraction hr d) (by positivity)
    _ ≤ _ := by
      have he := mul_le_mul_of_nonneg_left (damping_le_one hΛ hr.le) (abs_nonneg (θ - η))
      simpa only [mul_one] using mul_le_mul_of_nonneg_right he (norm_nonneg d)

theorem mean_pointwise_difference {Λ : ℝ} (hΛ : 0 ≤ Λ) (u d : CircleL2) (θ η : ℝ)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (x : HeatCircle) :
    |mean Λ u d (θ, (r, x)) - mean Λ u d (η, (r, x))| ≤
      Real.sqrt (1 + heatConstant) * r ^ (-(1 / 4 : ℝ)) * (|θ - η| * ‖d‖) := by
  rw [mean_difference, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h := mul_le_mul_of_nonneg_left (physicalHeatMean_pointwise hr hr1 d x)
    (show 0 ≤ |θ - η| * Real.exp (-Λ * r) by positivity)
  calc
    _ ≤ _ := h
    _ ≤ |θ - η| * (Real.sqrt (1 + heatConstant) * r ^ (-(1 / 4 : ℝ)) * ‖d‖) := by
      have he := damping_le_one hΛ hr.le
      have hn : 0 ≤ Real.sqrt (1 + heatConstant) * r ^ (-(1 / 4 : ℝ)) * ‖d‖ := by positivity
      nlinarith [mul_le_mul_of_nonneg_left he (abs_nonneg (θ - η))]
    _ = _ := by ring

variable (P : CanonicalCovariance.ProfileParameters)

def profile (Λ : ℝ) (u d : CircleL2) (p : ℝ × Domain) : ℝ :=
  ParametricProfile.canonicalProfile P.coefficient (mean Λ u d) P.lower P.horizon p

theorem profile_measurable (Λ : ℝ) (u d : CircleL2) : Measurable (profile P Λ u d) :=
  ParametricProfile.canonicalProfile_measurable P.measurable (mean_measurable Λ u d)
    P.lower_pos P.upper_nonneg P.holder_nonneg P.exponent_pos P.exponent_le_one
    P.horizon_pos P.horizon_le_one P.lower_bound P.upper_bound P.holder_bound P.small

theorem profile_bounds (Λ : ℝ) (u d : CircleL2) (p : ℝ × Domain) :
    P.lower ≤ profile P Λ u d p ∧ profile P Λ u d p ≤ P.upper :=
  ParametricProfile.canonicalProfile_elliptic P.measurable (mean_measurable Λ u d)
    P.lower_pos P.upper_nonneg P.holder_nonneg P.exponent_pos P.exponent_le_one
    P.horizon_pos P.horizon_le_one P.lower_bound P.upper_bound P.holder_bound P.small p

theorem profile_fixed (Λ : ℝ) (u d : CircleL2) (θ : ℝ) {r : ℝ}
    (hr : r ∈ Ioc 0 P.horizon) (x : HeatCircle) :
    profile P Λ u d (θ, (r, x)) = profileUpdate P.coefficient (fun p => mean Λ u d (θ, p))
      (fun p => profile P Λ u d (θ, p)) r x :=
  ParametricProfile.canonicalProfile_fixed P.measurable (mean_measurable Λ u d)
    P.lower_pos P.upper_nonneg P.holder_nonneg P.exponent_pos P.exponent_le_one
    P.horizon_pos P.horizon_le_one P.lower_bound P.upper_bound P.holder_bound P.small θ r hr x

theorem profile_outside (Λ : ℝ) (u d : CircleL2) (θ : ℝ) {p : Domain}
    (hp : p.1 ∉ Ioc 0 P.horizon) : profile P Λ u d (θ, p) = P.lower := by
  obtain ⟨c, hc, hb, hf⟩ := ScalarProfileFixedPoint.exists_scalar_profile P.measurable
    ((mean_measurable Λ u d).comp (measurable_const.prodMk measurable_id))
    P.lower_pos P.upper_nonneg P.holder_nonneg P.exponent_pos P.exponent_le_one
    P.horizon_pos P.horizon_le_one P.lower_bound P.upper_bound P.holder_bound P.small
  have h := ParametricProfile.canonicalProfile_eq_clipped P.measurable (mean_measurable Λ u d)
    P.lower_pos P.upper_nonneg P.holder_nonneg P.exponent_pos P.exponent_le_one
    P.horizon_pos P.horizon_le_one P.lower_bound P.upper_bound P.holder_bound P.small θ c hc hb hf p
  exact h.trans (ite_eq_right hp)

/-- Sharp spatial L² finite differences for the actual controlled profile.
The constant is independent of the damping scale. -/
theorem profile_l2_stability {Λ : ℝ} (hΛ : 0 ≤ Λ) (u d : CircleL2) (θ η : ℝ)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent *
      ProfileVolterra.powerConstant ((P.exponent - 1) / 4) * P.horizon ^ (P.exponent / 4) ≤ 1 / 2)
    {r : ℝ} (hr : r ∈ Ioc 0 P.horizon) :
    normTwo haarAddCircle (fun x => profile P Λ u d (θ, (r, x)) - profile P Λ u d (η, (r, x))) ≤
      2 * (meanConstant P.lower P.holder P.exponent * (|θ - η| * ‖d‖)) *
        r ^ ((P.exponent - 1) / 4) := by
  have hc : Measurable (fun p => profile P Λ u d (θ, p)) :=
    (profile_measurable P Λ u d).comp (measurable_const.prodMk measurable_id)
  have hd : Measurable (fun p => profile P Λ u d (η, p)) :=
    (profile_measurable P Λ u d).comp (measurable_const.prodMk measurable_id)
  have haB (z : ℝ) : |P.coefficient z| ≤ P.upper := by
    rw [abs_of_nonneg (P.lower_pos.le.trans (P.lower_bound z))]
    exact P.upper_bound z
  convert! (scalar_profile_l2_stability
    (φ := fun p => mean Λ u d (θ, p)) (ψ := fun p => mean Λ u d (η, p))
    (c := fun p => profile P Λ u d (θ, p)) (d := fun p => profile P Λ u d (η, p))
    P.measurable hc hd P.lower_pos P.upper_nonneg
    P.holder_nonneg P.exponent_pos P.exponent_le_one P.horizon_pos P.horizon_le_one
    (show 0 ≤ |θ - η| * ‖d‖ by positivity) haB P.holder_bound
    (fun p => profile_bounds P Λ u d (θ, p)) (fun p => profile_bounds P Λ u d (η, p))
    (fun r hr => mean_l2_difference hΛ u d θ η hr.1) hsmallL2
    (fun r hr x => profile_fixed P Λ u d θ hr x)
    (fun r hr x => profile_fixed P Λ u d η hr x) r hr).1 using 1

end SHE.ControlledProfile
