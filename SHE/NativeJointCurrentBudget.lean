module
public import SHE.NativeJointRowPositive
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
namespace SHE.NativeJointCurrentBudget
open Set MeasureTheory PredictableL2 Real AddCircle StoppedFourier NativeHeatObservation NativeMovingCurrentGamma ScalarGaussianSemigroup DyadicApproximation
open scoped NNReal ENNReal
local instance jointCurrentBudget_period : Fact (0<2*π):=⟨by positivity⟩
local instance jointCurrentBudget_realSigma : MeasurableSpace RealL2:=borel _
local instance jointCurrentBudget_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance jointCurrentBudget_unitPos : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance jointCurrentBudget_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance jointCurrentBudget_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance jointCurrentBudget_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance jointCurrentBudget_realSecond : SecondCountableTopology RealL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
variable {Ω:Type*} [MeasurableSpace Ω]

def value (μ:Measure Ω) (P:CanonicalCovariance.ProfileParameters) (U V:ℝ≥0×Ω→RealL2)
    (Λ:ℝ) (H:ℝ≥0) (a:ℝ→ℝ) (j:ℕ) (ρ h r:ℝ):ℝ≥0∞:=
  ∫⁻p:ℝ×(Ω×HeatCircle),ENNReal.ofReal
    (p.1^(ρ-1/2)*|NativeJointGradientFields.value P U V Λ H a j h (p.1,(r,p.2))|^2)
      ∂(volume.restrict (Ioc (0:ℝ) h)).prod (μ.prod haarAddCircle)

theorem measurable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω) [SFinite μ]
    (P:CanonicalCovariance.ProfileParameters) (U V:ℝ≥0×Ω→RealL2)
    (hU:StronglyMeasurable[𝓕.predictable] U) (hV:StronglyMeasurable[𝓕.predictable] V)
    (Λ:ℝ) (H:ℝ≥0) {a:ℝ→ℝ} (ha:SmoothCylinders.BoundedSmooth a) (j:ℕ) (ρ h:ℝ):
    Measurable (value μ P U V Λ H a j ρ h):=by
  have hG:=NativeJointGradientFields.measurable 𝓕 P U V hU hV Λ H ha j h
  have hm:Measurable (fun p:ℝ×(ℝ×(Ω×HeatCircle))=>ENNReal.ofReal
      (p.2.1^(ρ-1/2)*|NativeJointGradientFields.value P U V Λ H a j h (p.2.1,(p.1,p.2.2))|^2)):=by
    have hg:=hG.comp (measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd))
    have hs:Measurable (fun p:ℝ×(ℝ×(Ω×HeatCircle))=>
        |NativeJointGradientFields.value P U V Λ H a j h (p.2.1,(p.1,p.2.2))|^2):=by
      simpa only [Real.norm_eq_abs,Function.comp_apply] using hg.norm.pow_const 2
    exact ((by fun_prop:Measurable (fun p:ℝ×(ℝ×(Ω×HeatCircle))=>p.2.1^(ρ-1/2))).mul hs).ennreal_ofReal
  exact hm.lintegral_prod_right

/-- The direct jointly Borel current budget is EXACTLY the original
native row slot at every covered moving past; this is not a bound by
an independently chosen current law. -/
theorem native_eq (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω) [IsProbabilityMeasure μ]
    (P:CanonicalCovariance.ProfileParameters) (H:ℝ≥0) (U V:ℝ≥0×Ω→RealL2)
    (hU:StronglyMeasurable[𝓕.predictable] U) (hV:StronglyMeasurable[𝓕.predictable] V)
    (Λ:ℝ) {a:ℝ→ℝ} (ha:SmoothCylinders.BoundedSmooth a) {A:ℝ} (hA:0≤A)
    (hh:∀x y,|a x-a y|≤A*|x-y|^P.exponent) (j:ℕ) (ρ:ℝ)
    {v h:ℝ} (hv:0<v) (hvh:v+h≤H):
    value μ P U V Λ H a j ρ h v=
      ∫⁻τ in Ioc (0:ℝ) h,∫⁻ω,ENNReal.ofReal (τ^(ρ-1/2)*‖NativeRandomRows.nativeRow
        (NativeJointRowClock.field P U V Λ v.toNNReal (v+h).toNNReal a j 0) ((v+h-τ).toNNReal,ω)-
          NativeRandomRows.nativeRow (NativeJointRowClock.field P U V Λ v.toNNReal (v+h).toNNReal a j 1)
            ((v+h-τ).toNNReal,ω)‖^2) ∂μ:=by
  let C:=ScalarHeatSingleMultiplier.cap A P.exponent j
  let G:=NativeJointGradientFields.value P U V Λ H a j h
  have hC:0≤C:=by
    unfold C ScalarHeatSingleMultiplier.cap
    have hc:=ScalarGaussianJetScale.constant_nonneg P.exponent 0
    have hr:=CompactMollifier.radius_pos (j+1)
    positivity
  have hG:Measurable G:=NativeJointGradientFields.measurable 𝓕 P U V hU hV Λ H ha j h
  have hGb(p):|G p|≤2*C:=NativeJointGradientFields.bound P U V Λ H ha hA hh j h p
  have hGs:Measurable (fun p=>|G p|^2):=by simpa only [Real.norm_eq_abs] using hG.norm.pow_const 2
  have hm:Measurable (fun p:ℝ×(Ω×HeatCircle)=>ENNReal.ofReal (p.1^(ρ-1/2)*|G (p.1,(v,p.2))|^2)):=
    ((by fun_prop:Measurable (fun p:ℝ×(Ω×HeatCircle)=>p.1^(ρ-1/2))).mul
      (hGs.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))).ennreal_ofReal
  rw [value,lintegral_prod _ hm.aemeasurable]
  apply lintegral_congr_ae
  have hmem:∀ᵐτ∂volume.restrict (Ioc (0:ℝ) h),τ∈Ioo (0:ℝ) h:=by
    rw [←restrict_Ioo_eq_restrict_Ioc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hmem] with τ ht
  let F0:=NativeJointRowClock.field P U V Λ v.toNNReal (v+h).toNNReal a j 0
  let F1:=NativeJointRowClock.field P U V Λ v.toNNReal (v+h).toNNReal a j 1
  have hm0:=NativeJointRowClock.field_measurable 𝓕 P U V hU hV Λ v.toNNReal (v+h).toNNReal ha j 0
  have hm1:=NativeJointRowClock.field_measurable 𝓕 P U V hU hV Λ v.toNNReal (v+h).toNNReal ha j 1
  have hb(θ:ℝ)(p)(x):‖NativeJointRowClock.field P U V Λ v.toNNReal (v+h).toNNReal a j θ (p,x)‖≤C:=
    ScalarHeatSingleMultiplier.field_bound ha hA P.exponent_pos.le P.exponent_le_one hh j _ _ p x
  have hiG:Integrable (fun z:Ω×HeatCircle=>|G (τ,(v,z))|^2) (μ.prod haarAddCircle):=by
    apply (integrable_const ((2*C)^2)).mono'
      ((hGs.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aestronglyMeasurable)
    exact ae_of_all _ (fun z=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hGb _) 2)
  rw [←ofReal_integral_eq_lintegral_ofReal (hiG.const_mul (τ^(ρ-1/2)))
    (ae_of_all _ (fun _=>mul_nonneg (Real.rpow_nonneg ht.1.le _) (sq_nonneg _))),integral_const_mul]
  rw [NativeRowEnergyCast.sample μ F0 F1 hm0 hm1 hC (hb 0) (hb 1) (Real.rpow_nonneg ht.1.le _)]
  rw [NativeJointRowClock.energy_eq 𝓕 μ P U V hU hV Λ H ha hA hh j hv hvh ht]
  rfl

/-- The measurable direct budget has the actual sharp global current
energy cap, with original past integration before clipping. -/
theorem energy (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω) [IsProbabilityMeasure μ]
    (P:CanonicalCovariance.ProfileParameters) (H:ℝ≥0) (U V:ℝ≥0×Ω→RealL2)
    (hU:StronglyMeasurable[𝓕.predictable] U) (hV:StronglyMeasurable[𝓕.predictable] V)
    (hi:Integrable (fun z=>‖V z-U z‖^2) ((PredictableL2.timeMeasure H).prod μ))
    {Λ h W ρ A:ℝ} (hΛ:0≤Λ) (hh:0<h) (hh1:h≤1) (hW:0≤W) (hW1:W≤1) (hcover:W+h≤H)
    (hρ0:-(1/2:ℝ)<ρ) (hρ1:ρ<1/2) {a:ℝ→ℝ} (ha:SmoothCylinders.BoundedSmooth a) (hA:0≤A)
    (hholder:∀x y,|a x-a y|≤A*|x-y|^P.exponent) (j:ℕ):
    (∫⁻r in Ioc (0:ℝ) W,value μ P U V Λ H a j ρ h r)≤
      ENNReal.ofReal ((2*A*ScalarHeatGradientDifference.constant P.exponent)^2*
        ScalarHeatBandTime.massConstant P.exponent ρ*(ProfileVariance.lowerConstant*P.lower)^(-1-2*ρ)*
          CompactMollifier.radius (j+1)^(2*P.exponent+4*ρ)*
            min 1 ((4*∫z,‖V z-U z‖^2 ∂((PredictableL2.timeMeasure H).prod μ))/CompactMollifier.radius (j+1)^2)):=by
  have hb:=NativeJointRowPositive.energy 𝓕 μ P H U V hU hV hi hΛ hh hh1 hW hW1 hcover hρ0 hρ1 ha hA hholder j
  apply le_trans _ hb
  apply le_of_eq
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  exact native_eq 𝓕 μ P H U V hU hV Λ ha hA hholder j ρ hr.1 (by linarith [hr.2,hcover])

end SHE.NativeJointCurrentBudget
