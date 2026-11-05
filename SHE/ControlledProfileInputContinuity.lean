module

public import SHE.ControlledProfileFamilies

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.ControlledProfileInputContinuity
open Set MeasureTheory AddCircle StoppedFourier ProfileVariance PhysicalProfile
open ControlledProfile ProfileStability ProfilePointwise ProfileMeanPointwise
open scoped NNReal Topology
local instance controlledProfileInputContinuity_period : Fact (0<2*Real.pi) := ⟨by positivity⟩

theorem mean_input_difference {Λ : ℝ} (hΛ : 0≤Λ) (u d u' d' : CircleL2) (θ : ℝ)
    {r : ℝ} (hr : 0<r) (hr1 : r≤1) (x : HeatCircle) :
    |mean Λ u d (θ,(r,x))-mean Λ u' d' (θ,(r,x))|≤
      Real.sqrt (1+heatConstant)*r^(-(1/4:ℝ))*(‖u-u'‖+|θ| *‖d-d'‖) := by
  let A := Real.sqrt (1+heatConstant)*r^(-(1/4:ℝ))
  have hA : 0≤A := by dsimp [A]; positivity
  have hu : |physicalHeatMean u (r,x)-physicalHeatMean u' (r,x)|≤A*‖u-u'‖ := by
    rw [physicalHeatMean_difference hr]
    exact physicalHeatMean_pointwise hr hr1 _ x
  have hd : |physicalHeatMean d (r,x)-physicalHeatMean d' (r,x)|≤A*‖d-d'‖ := by
    rw [physicalHeatMean_difference hr]
    exact physicalHeatMean_pointwise hr hr1 _ x
  have he := ControlledProfile.damping_le_one hΛ hr.le
  have hx : mean Λ u d (θ,(r,x))-mean Λ u' d' (θ,(r,x))=
      (physicalHeatMean u (r,x)-physicalHeatMean u' (r,x))+
        (θ*Real.exp (-Λ*r))*(physicalHeatMean d (r,x)-physicalHeatMean d' (r,x)) := by
    unfold mean
    ring
  rw [hx]
  calc
    _ ≤ |physicalHeatMean u (r,x)-physicalHeatMean u' (r,x)|+
        |(θ*Real.exp (-Λ*r))*(physicalHeatMean d (r,x)-physicalHeatMean d' (r,x))| := abs_add_le _ _
    _ ≤ A*‖u-u'‖+(|θ| *Real.exp (-Λ*r))*(A*‖d-d'‖) := by
      rw [abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
      exact add_le_add hu (mul_le_mul_of_nonneg_left hd (by positivity))
    _ ≤ A*‖u-u'‖+|θ| *(A*‖d-d'‖) := by
      gcongr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left he (abs_nonneg θ)
    _ = _ := by dsimp [A]; ring

variable (P : CanonicalCovariance.ProfileParameters)

/-- Actual canonical controlled profiles are Lipschitz in BOTH original
L² states, uniformly in damping at each fixed positive age. -/
theorem profile_input_bound {Λ : ℝ} (hΛ : 0≤Λ) (u d u' d' : CircleL2) (θ : ℝ)
    (hsmall : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    {r : ℝ} (hr : r∈Ioc 0 P.horizon) (x : HeatCircle) :
    |profile P Λ u d (θ,(r,x))-profile P Λ u' d' (θ,(r,x))|≤
      2*(meanConstant P.lower P.holder P.exponent*Real.sqrt (1+heatConstant)*
        (‖u-u'‖+|θ| *‖d-d'‖))*r^((P.exponent-2)/4) := by
  have hc : Measurable (fun z => profile P Λ u d (θ,z)) :=
    (profile_measurable P Λ u d).comp (measurable_const.prodMk measurable_id)
  have hd : Measurable (fun z => profile P Λ u' d' (θ,z)) :=
    (profile_measurable P Λ u' d').comp (measurable_const.prodMk measurable_id)
  have haB (z : ℝ) : |P.coefficient z|≤P.upper := by
    rw [abs_of_nonneg (P.lower_pos.le.trans (P.lower_bound z))]
    exact P.upper_bound z
  exact scalar_profile_pointwise_stability P.measurable hc hd P.lower_pos P.upper_nonneg
    P.holder_nonneg P.exponent_pos P.exponent_le_one P.horizon_pos P.horizon_le_one
    (by positivity) haB P.holder_bound
    (fun z => profile_bounds P Λ u d (θ,z)) (fun z => profile_bounds P Λ u' d' (θ,z))
    (fun r hr x => mean_input_difference hΛ u d u' d' θ hr.1 (hr.2.trans P.horizon_le_one) x)
    hsmall (fun r hr x => profile_fixed P Λ u d θ hr x)
    (fun r hr x => profile_fixed P Λ u' d' θ hr x) r hr x

theorem profile_inputs_continuous {Λ : ℝ} (hΛ : 0≤Λ) (θ : ℝ)
    (hsmall : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (z : Domain) : Continuous (fun p : Inputs => profile P Λ p.1 p.2 (θ,z)) := by
  by_cases hz : z.1∈Ioc 0 P.horizon
  · have hz0 : 0≤z.1 := hz.1.le
    let K := 2*(meanConstant P.lower P.holder P.exponent*Real.sqrt (1+heatConstant))*
      z.1^((P.exponent-2)/4)*(1+|θ|)
    have hK : 0≤K := by
      dsimp [K]
      positivity [heatConstant_pos,meanConstant_nonneg (β := P.exponent) P.lower_pos.le P.holder_nonneg]
    apply (LipschitzWith.of_dist_le_mul (K := ⟨K,hK⟩) ?_).continuous
    intro p q
    have hh := profile_input_bound P hΛ p.1 p.2 q.1 q.2 θ hsmall hz z.2
    rw [Real.dist_eq,dist_eq_norm]
    apply hh.trans
    have hu : ‖p.1-q.1‖≤‖p-q‖ := norm_fst_le (p-q)
    have hd : ‖p.2-q.2‖≤‖p-q‖ := norm_snd_le (p-q)
    have hD : ‖p.1-q.1‖+|θ| *‖p.2-q.2‖≤(1+|θ|)*‖p-q‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hd (abs_nonneg θ)]
    change 2*(meanConstant P.lower P.holder P.exponent*Real.sqrt (1+heatConstant)*
      (‖p.1-q.1‖+|θ| *‖p.2-q.2‖))*z.1^((P.exponent-2)/4)≤K*‖p-q‖
    dsimp [K]
    have hC : 0≤2*(meanConstant P.lower P.holder P.exponent*Real.sqrt (1+heatConstant))*z.1^((P.exponent-2)/4) := by
      positivity [heatConstant_pos,meanConstant_nonneg (β := P.exponent) P.lower_pos.le P.holder_nonneg]
    nlinarith [mul_le_mul_of_nonneg_left hD hC]
  · have he : (fun p : Inputs => profile P Λ p.1 p.2 (θ,z))=fun _ => P.lower := by
      funext p
      exact profile_outside P Λ p.1 p.2 θ hz
    rw [he]
    exact continuous_const

end SHE.ControlledProfileInputContinuity
