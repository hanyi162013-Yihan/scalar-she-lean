module
public import SHE.ControlledResidualField
public import SHE.ControlledProfileInputContinuity

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SHE.ControlledResidualContinuity
open Set MeasureTheory AddCircle StoppedFourier ControlledProfile ProfileL2 Filter Topology
local instance period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeSigma : MeasurableSpace CircleL2:=borel _
local instance nativeBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
variable(P:CanonicalCovariance.ProfileParameters){Λ:ℝ}(hΛ:0≤Λ)(κ θ:ℝ)(hκ:κ<P.lower)
variable(hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

include hΛ hκ hsmall in
/-- Strong L2 continuity of the actual residual coefficient in both
frozen past states, before any stochastic integral is evaluated. -/
theorem native (r:ℝ):Continuous (fun p:Inputs=>ControlledResidualField.native P Λ κ ((p,θ),r)):=by
  rw [continuous_iff_continuousAt]
  intro p
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
  let diff (q:Inputs)(x:HeatCircle):ℝ:=profile P Λ q.1 q.2 (θ,(r,x))-profile P Λ p.1 p.2 (θ,(r,x))
  have hm(q:Inputs):Measurable (diff q):=by
    exact (((profile_measurable P Λ q.1 q.2).sub (profile_measurable P Λ p.1 p.2)).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
  have hb(q:Inputs)(x:HeatCircle):|diff q x|≤2*P.upper:=by
    have hq:=profile_bounds P Λ q.1 q.2 (θ,(r,x))
    have hp:=profile_bounds P Λ p.1 p.2 (θ,(r,x))
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg (P.lower_pos.le.trans hq.1),
      abs_of_nonneg (P.lower_pos.le.trans hp.1)];linarith)
  have hc:Continuous (fun q:Inputs=>∫x:HeatCircle,(diff q x)^2 ∂haarAddCircle):=by
    apply continuous_of_dominated (bound:=fun _:HeatCircle=>(2*P.upper)^2)
    · intro q
      exact ((hm q).pow_const 2).aestronglyMeasurable
    · intro q
      filter_upwards with x
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (diff q x)) (hb q x) 2
    · exact integrable_const _
    · filter_upwards with x
      exact ((ControlledProfileInputContinuity.profile_inputs_continuous P hΛ θ hsmall (r,x)).sub continuous_const).pow 2
  have hnorm(q:Inputs):‖ControlledResidualField.native P Λ κ ((q,θ),r)-
      ControlledResidualField.native P Λ κ ((p,θ),r)‖=Real.sqrt (∫x:HeatCircle,(diff q x)^2 ∂haarAddCircle):=by
    have he:=MeasurableL2Field.real_l2_diff_norm
      (ControlledResidualField.native_ae P Λ κ hκ ((q,θ),r))
      (ControlledResidualField.native_ae P Λ κ hκ ((p,θ),r))
    convert! he using 1
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    dsimp [ControlledResidualField.scalar,diff]
    ring
  have ht:=Real.continuous_sqrt.continuousAt.tendsto.comp (hc.tendsto p)
  have hz:(∫x:HeatCircle,(diff p x)^2 ∂haarAddCircle)=0:=by simp [diff]
  simp only [hz,Real.sqrt_zero] at ht
  exact ht.congr' (Eventually.of_forall (fun q=>(hnorm q).symm))

include hΛ hκ hsmall in
theorem field (r:ℝ):Continuous (fun p:Inputs=>ControlledResidualField.field P Λ κ hκ ((p,θ),r)):=by
  apply Continuous.subtype_mk
  exact CircleNormalization.push.symm.continuous.comp (native P hΛ κ θ hκ hsmall r)

end SHE.ControlledResidualContinuity
