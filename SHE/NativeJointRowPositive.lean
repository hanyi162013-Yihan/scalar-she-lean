module
public import SHE.NativeJointRowTime
public import SHE.NativeJointGradientFields
public import SHE.NativeRowEnergyCast
public import SHE.PositiveSectionCast
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
namespace SHE.NativeJointRowPositive
open Set MeasureTheory PredictableL2 Real AddCircle StoppedFourier NativeHeatObservation NativeMovingCurrentGamma ScalarGaussianSemigroup DyadicApproximation
open scoped NNReal ENNReal
local instance jointRowPositive_period : Fact (0<2*π):=⟨by positivity⟩
local instance jointRowPositive_realSigma : MeasurableSpace RealL2:=borel _
local instance jointRowPositive_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance jointRowPositive_unitPos : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance jointRowPositive_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance jointRowPositive_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance jointRowPositive_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance jointRowPositive_realSecond : SecondCountableTopology RealL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
variable {Ω:Type*} [MeasurableSpace Ω]

/-- The sharp joint-current cap on the ORIGINAL positive iterated
past/age/sample integral. Past averaging occurs before clipping, and
all changes of integral convention and integration order are proved. -/
theorem energy (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω) [IsProbabilityMeasure μ]
    (P:CanonicalCovariance.ProfileParameters) (H:ℝ≥0) (U V:ℝ≥0×Ω→RealL2)
    (hU:StronglyMeasurable[𝓕.predictable] U) (hV:StronglyMeasurable[𝓕.predictable] V)
    (hi:Integrable (fun z=>‖V z-U z‖^2) ((PredictableL2.timeMeasure H).prod μ))
    {Λ h W ρ A:ℝ} (hΛ:0≤Λ) (hh:0<h) (hh1:h≤1) (hW:0≤W) (hW1:W≤1) (hcover:W+h≤H)
    (hρ0:-(1/2:ℝ)<ρ) (hρ1:ρ<1/2) {a:ℝ→ℝ} (ha:SmoothCylinders.BoundedSmooth a) (hA:0≤A)
    (hholder:∀x y,|a x-a y|≤A*|x-y|^P.exponent) (j:ℕ):
    (∫⁻v in Ioc (0:ℝ) W,∫⁻τ in Ioc (0:ℝ) h,∫⁻ω,
      ENNReal.ofReal (τ^(ρ-1/2)*‖NativeRandomRows.nativeRow
        (NativeJointRowClock.field P U V Λ v.toNNReal (v+h).toNNReal a j 0) ((v+h-τ).toNNReal,ω)-
          NativeRandomRows.nativeRow (NativeJointRowClock.field P U V Λ v.toNNReal (v+h).toNNReal a j 1)
            ((v+h-τ).toNNReal,ω)‖^2) ∂μ)≤
      ENNReal.ofReal ((2*A*ScalarHeatGradientDifference.constant P.exponent)^2*
        ScalarHeatBandTime.massConstant P.exponent ρ*(ProfileVariance.lowerConstant*P.lower)^(-1-2*ρ)*
          CompactMollifier.radius (j+1)^(2*P.exponent+4*ρ)*
            min 1 ((4*∫z,‖V z-U z‖^2 ∂((PredictableL2.timeMeasure H).prod μ))/CompactMollifier.radius (j+1)^2)):=by
  let C:=ScalarHeatSingleMultiplier.cap A P.exponent j
  have hC:0≤C:=by
    unfold C ScalarHeatSingleMultiplier.cap
    have hc:=ScalarGaussianJetScale.constant_nonneg P.exponent 0
    have hr:=CompactMollifier.radius_pos (j+1)
    positivity
  let G:=NativeJointGradientFields.value P U V Λ H a j h
  have hG:Measurable G:=NativeJointGradientFields.measurable 𝓕 P U V hU hV Λ H ha j h
  have hGb(p):|G p|≤2*C:=NativeJointGradientFields.bound P U V Λ H ha hA hholder j h p
  have hGs:Measurable (fun p=>|G p|^2):=by simpa only [Real.norm_eq_abs] using hG.norm.pow_const 2
  let f:ℝ×ℝ→ℝ:=fun p=>p.1^(ρ-1/2)*(∫z:Ω×HeatCircle,|G (p.1,(p.2,z))|^2 ∂μ.prod haarAddCircle)
  have hm0:Measurable (fun p:(ℝ×ℝ)×(Ω×HeatCircle)=>|G (p.1.1,(p.1.2,p.2))|^2):=
    hGs.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have hm:Measurable f:=by
    have ht:Measurable (fun p:ℝ×ℝ=>p.1^(ρ-1/2)):=by fun_prop
    exact ht.mul hm0.stronglyMeasurable.integral_prod_right'.measurable
  have hiG(τ v:ℝ):Integrable (fun z:Ω×HeatCircle=>|G (τ,(v,z))|^2) (μ.prod haarAddCircle):=by
    apply (integrable_const ((2*C)^2)).mono'
      ((hGs.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aestronglyMeasurable)
    exact ae_of_all _ (fun z=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hGb _) 2)
  have hfi(τ:ℝ):IntegrableOn (fun v=>f (τ,v)) (Ioc (0:ℝ) W):=by
    apply (integrable_const (|τ^(ρ-1/2)| *(2*C)^2)).mono'
      ((hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    apply ae_of_all
    intro v
    have hb:(∫z:Ω×HeatCircle,|G (τ,(v,z))|^2 ∂μ.prod haarAddCircle)≤(2*C)^2:=by
      simpa [integral_const,measureReal_def] using
        integral_mono_ae (hiG τ v) (integrable_const ((2*C)^2))
          (ae_of_all _ (fun z=>pow_le_pow_left₀ (abs_nonneg _) (hGb _) 2))
    change ‖f (τ,v)‖≤_
    rw [Real.norm_eq_abs,show f (τ,v)=τ^(ρ-1/2)*(∫z:Ω×HeatCircle,|G (τ,(v,z))|^2 ∂μ.prod haarAddCircle) from rfl,
      abs_mul,abs_of_nonneg (integral_nonneg (fun _=>sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
  have hmem:∀ᵐτ∂volume.restrict (Ioc (0:ℝ) h),τ∈Ioo (0:ℝ) h:=by
    rw [←restrict_Ioo_eq_restrict_Ioc]
    exact ae_restrict_mem measurableSet_Ioo
  have hrow(τ)(ht:τ∈Ioo (0:ℝ) h):
      (∫v in Ioc (0:ℝ) W,f (τ,v))=τ^(ρ-1/2)*NativeJointRowTime.rowEnergy μ P U V Λ a j W h τ:=by
    rw [show (fun v=>f (τ,v))=(fun v=>τ^(ρ-1/2)*(∫z:Ω×HeatCircle,|G (τ,(v,z))|^2 ∂μ.prod haarAddCircle)) from rfl,
      integral_const_mul]
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact (NativeJointRowClock.energy_eq 𝓕 μ P U V hU hV Λ H ha hA hholder j hv.1
      (by linarith [hv.2,hcover]) ht).symm
  have hb:=NativeJointRowTime.energy 𝓕 μ P H U V hU hV hi hΛ hh hh1 hW hW1 hcover hρ0 hρ1 ha hA hholder j
  have he:(fun τ=>∫v in Ioc (0:ℝ) W,f (τ,v))=ᵐ[volume.restrict (Ioc (0:ℝ) h)]
      (fun τ=>τ^(ρ-1/2)*NativeJointRowTime.rowEnergy μ P U V Λ a j W h τ):=hmem.mono (fun τ ht=>hrow τ ht)
  have hswap:=PositiveSectionCast.swap (volume.restrict (Ioc (0:ℝ) h)) (volume.restrict (Ioc (0:ℝ) W)) f hm
    (ae_of_all _ hfi) (hb.1.congr he.symm) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ ht
      exact ae_of_all _ (fun v=>mul_nonneg (Real.rpow_nonneg ht.1.le _) (integral_nonneg (fun _=>sq_nonneg _))))
  calc
    _=(∫⁻v in Ioc (0:ℝ) W,∫⁻τ in Ioc (0:ℝ) h,ENNReal.ofReal (f (τ,v))):=by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      apply lintegral_congr_ae
      filter_upwards [hmem] with τ ht
      let F0:=NativeJointRowClock.field P U V Λ v.toNNReal (v+h).toNNReal a j 0
      let F1:=NativeJointRowClock.field P U V Λ v.toNNReal (v+h).toNNReal a j 1
      have hm0:=NativeJointRowClock.field_measurable 𝓕 P U V hU hV Λ v.toNNReal (v+h).toNNReal ha j 0
      have hm1:=NativeJointRowClock.field_measurable 𝓕 P U V hU hV Λ v.toNNReal (v+h).toNNReal ha j 1
      have hbound(θ:ℝ)(p)(x):‖NativeJointRowClock.field P U V Λ v.toNNReal (v+h).toNNReal a j θ (p,x)‖≤C:=
        ScalarHeatSingleMultiplier.field_bound ha hA P.exponent_pos.le P.exponent_le_one hholder j _ _ p x
      rw [NativeRowEnergyCast.sample μ F0 F1 hm0 hm1 hC (hbound 0) (hbound 1) (Real.rpow_nonneg ht.1.le _)]
      rw [NativeJointRowClock.energy_eq 𝓕 μ P U V hU hV Λ H ha hA hholder j hv.1 (by linarith [hv.2,hcover]) ht]
      rfl
    _=ENNReal.ofReal (∫τ in Ioc (0:ℝ) h,∫v in Ioc (0:ℝ) W,f (τ,v)):=hswap
    _=ENNReal.ofReal (∫τ in Ioc (0:ℝ) h,τ^(ρ-1/2)*NativeJointRowTime.rowEnergy μ P U V Λ a j W h τ):=
      congrArg ENNReal.ofReal (integral_congr_ae he)
    _≤_:=ENNReal.ofReal_le_ofReal hb.2
end SHE.NativeJointRowPositive
