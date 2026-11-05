module

public import SHE.ControlledProfile
public import SHE.ProfileMeanPointwise
public import SHE.ProfileParameter

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

/-! Actual pointwise parameter stability for the prescribed damped mean
profile. Coarse pointwise bounds are used for dominated differentiation;
the separate sharp spatial L² stability remains unchanged. -/
namespace SHE.ControlledProfile
open Set MeasureTheory AddCircle StoppedFourier ProfileVariance GaussianProfile
  ProfileStability ProfilePointwise ProfileMeanPointwise ProfileParameter
open scoped NNReal Topology
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable (P : CanonicalCovariance.ProfileParameters)

theorem profile_pointwise_stability {Λ : ℝ} (hΛ : 0 ≤ Λ) (u d : CircleL2) (θ η : ℝ)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent *
      ProfileVolterra.powerConstant ((P.exponent - 2) / 4) * P.horizon ^ (P.exponent / 4) ≤ 1 / 2)
    {r : ℝ} (hr : r ∈ Ioc 0 P.horizon) (x : HeatCircle) :
    |profile P Λ u d (θ, (r, x)) - profile P Λ u d (η, (r, x))| ≤
      pointwiseConstant P.lower P.holder P.exponent r d * |θ - η| := by
  have hc : Measurable (fun p => profile P Λ u d (θ, p)) :=
    (profile_measurable P Λ u d).comp (measurable_const.prodMk measurable_id)
  have hd : Measurable (fun p => profile P Λ u d (η, p)) :=
    (profile_measurable P Λ u d).comp (measurable_const.prodMk measurable_id)
  have haB (z : ℝ) : |P.coefficient z| ≤ P.upper := by
    rw [abs_of_nonneg (P.lower_pos.le.trans (P.lower_bound z))]
    exact P.upper_bound z
  have h := scalar_profile_pointwise_stability
    (φ := fun p => mean Λ u d (θ, p)) (ψ := fun p => mean Λ u d (η, p))
    (c := fun p => profile P Λ u d (θ, p)) (d := fun p => profile P Λ u d (η, p))
    P.measurable hc hd P.lower_pos P.upper_nonneg P.holder_nonneg P.exponent_pos
    P.exponent_le_one P.horizon_pos P.horizon_le_one (show 0 ≤ |θ - η| * ‖d‖ by positivity)
    haB P.holder_bound (fun p => profile_bounds P Λ u d (θ, p))
    (fun p => profile_bounds P Λ u d (η, p))
    (fun r hr x => mean_pointwise_difference hΛ u d θ η hr.1 (hr.2.trans P.horizon_le_one) x)
    hsmallPoint (fun r hr x => profile_fixed P Λ u d θ hr x)
    (fun r hr x => profile_fixed P Λ u d η hr x) r hr x
  convert! h using 1
  unfold pointwiseConstant
  ring

theorem profile_curve_lipschitz {Λ : ℝ} (hΛ : 0 ≤ Λ) (u d : CircleL2)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent *
      ProfileVolterra.powerConstant ((P.exponent - 2) / 4) * P.horizon ^ (P.exponent / 4) ≤ 1 / 2)
    (p : Domain) :
    LipschitzWith ⟨curveBound P.lower P.holder P.exponent P.horizon d p,
      curveBound_nonneg P.lower_pos.le P.holder_nonneg d p⟩
      (fun θ => profile P Λ u d (θ, p)) := by
  apply LipschitzWith.of_dist_le_mul
  intro θ η
  rw [Real.dist_eq, Real.dist_eq]
  change |profile P Λ u d (θ, p) - profile P Λ u d (η, p)| ≤
    curveBound P.lower P.holder P.exponent P.horizon d p * |θ - η|
  by_cases hp : p.1 ∈ Ioc 0 P.horizon
  · rw [curveBound, ite_eq_left hp]
    exact profile_pointwise_stability P hΛ u d θ η hsmallPoint hp p.2
  · rw [profile_outside P Λ u d θ hp, profile_outside P Λ u d η hp,
      sub_self, abs_zero, curveBound, ite_eq_right hp, zero_mul]

end SHE.ControlledProfile
