module
public import SHE.NativeJointRowClock
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
namespace SHE.NativeJointRowTime
open Set MeasureTheory PredictableL2 Real AddCircle StoppedFourier NativeHeatObservation NativeMovingCurrentGamma ScalarGaussianSemigroup DyadicApproximation
open scoped NNReal ENNReal
local instance nativeJointRowTime_period : Fact (0<2*π):=⟨by positivity⟩
local instance nativeJointRowTime_realSigma : MeasurableSpace RealL2:=borel _
local instance nativeJointRowTime_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance nativeJointRowTime_unitPos : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeJointRowTime_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeJointRowTime_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance nativeJointRowTime_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance nativeJointRowTime_realSecond : SecondCountableTopology RealL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
variable {Ω:Type*} [MeasurableSpace Ω]

def rowEnergy (μ:Measure Ω) (P:CanonicalCovariance.ProfileParameters) (U V:ℝ≥0×Ω→RealL2)
    (Λ:ℝ) (a:ℝ→ℝ) (j:ℕ) (W h τ:ℝ):ℝ:=
  ∫v in Ioc (0:ℝ) W,∫ω,
    ‖NativeRandomRows.nativeRow (NativeJointRowClock.field P U V Λ v.toNNReal (v+h).toNNReal a j 0) ((v+h-τ).toNNReal,ω)-
      NativeRandomRows.nativeRow (NativeJointRowClock.field P U V Λ v.toNNReal (v+h).toNNReal a j 1) ((v+h-τ).toNNReal,ω)‖^2 ∂μ

/-- The actual joint-current native multiplier slot, with past
integration BEFORE clipping, has the sharp full Gaussian-band frequency
gain. The two state processes may be dependent, and their true joint
integrated difference energy is the only energy on the right. -/
theorem energy (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω) [IsProbabilityMeasure μ]
    (P:CanonicalCovariance.ProfileParameters) (H:ℝ≥0) (U V:ℝ≥0×Ω→RealL2)
    (hU:StronglyMeasurable[𝓕.predictable] U) (hV:StronglyMeasurable[𝓕.predictable] V)
    (hi:Integrable (fun z=>‖V z-U z‖^2) ((PredictableL2.timeMeasure H).prod μ))
    {Λ h W ρ A:ℝ} (hΛ:0≤Λ) (hh:0<h) (hh1:h≤1) (hW:0≤W) (hW1:W≤1) (hcover:W+h≤H)
    (hρ0:-(1/2:ℝ)<ρ) (hρ1:ρ<1/2) {a:ℝ→ℝ} (ha:SmoothCylinders.BoundedSmooth a) (hA:0≤A)
    (hholder:∀x y,|a x-a y|≤A*|x-y|^P.exponent) (j:ℕ):
    IntegrableOn (fun τ=>τ^(ρ-1/2)*rowEnergy μ P U V Λ a j W h τ) (Ioc (0:ℝ) h) ∧
      (∫τ in Ioc (0:ℝ) h,τ^(ρ-1/2)*rowEnergy μ P U V Λ a j W h τ)≤
        (2*A*ScalarHeatGradientDifference.constant P.exponent)^2*
          ScalarHeatBandTime.massConstant P.exponent ρ*(ProfileVariance.lowerConstant*P.lower)^(-1-2*ρ)*
          (CompactMollifier.radius (j+1))^(2*P.exponent+4*ρ)*
            min 1 ((4*∫z,‖V z-U z‖^2 ∂((PredictableL2.timeMeasure H).prod μ))/(CompactMollifier.radius (j+1))^2):=by
  let Ur:=fun z:ℝ×Ω=>U (z.1.toNNReal,z.2)
  let Dr:=NativePathZeroExtension.extend H (fun p=>V p-U p)
  have hmU:Measurable U:=(hU.mono (predictable_le_product 𝓕)).measurable
  have hmV:Measurable V:=(hV.mono (predictable_le_product 𝓕)).measurable
  have hUr:Measurable Ur:=hmU.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hDr:Measurable Dr:=NativePathZeroExtension.measurable H _ (hmV.sub hmU)
  have hDE:=NativePathZeroExtension.energy μ H (fun z=>V z-U z) (hmV.sub hmU) hi
  let ν:=((volume.restrict (Ioc (0:ℝ) W)).prod μ).prod (haarAddCircle (T:=2*π))
  let σ:=NativeMovingCurrentGamma.variance P Ur Dr Λ h 0
  let x:=current Ur h
  let y:=fun p=>x p+NativeMovingJointGamma.direction Dr Λ h p
  let g:=fun p=>deriv (heat (σ p).toNNReal (ScalarHeatBands.band a (j+1))) (y p)-
    deriv (heat (σ p).toNNReal (ScalarHeatBands.band a (j+1))) (x p)
  have hs:Measurable σ:=NativeMovingCurrentGamma.variance_measurable P Ur Dr hUr hDr Λ h 0
  have hx:Measurable x:=current_measurable Ur hUr h
  have hy:Measurable y:=hx.add (NativeMovingJointGamma.direction_measurable Dr hDr Λ h)
  have hg:Measurable g:=
    (PolynomialGaussianDecay.derivative_measurable ha (j+1) σ y hs hy).sub
      (PolynomialGaussianDecay.derivative_measurable ha (j+1) σ x hs hx)
  have hgs:Measurable (fun p=>|g p|^2):=by
    simpa only [Real.norm_eq_abs] using hg.norm.pow_const 2
  let C:=ScalarHeatSingleMultiplier.cap A P.exponent j
  have hgb(p:ℝ×space Ω):|g p|≤2*C:=by
    have hb(t:ℝ):|deriv (heat (σ p).toNNReal (ScalarHeatBands.band a (j+1))) t|≤C:=by
      simpa only [C,ScalarHeatSingleMultiplier.cap,iteratedDeriv_one,Nat.zero_add,Nat.cast_zero,sub_zero] using
        ScalarHeatBandJets.heated_positive_jet ha hA P.exponent_pos.le P.exponent_le_one hholder (σ p).toNNReal (j+1) 0 t
    exact (abs_sub _ _).trans ((add_le_add (hb _) (hb _)).trans_eq (by ring))
  have hiSection(τ:ℝ):Integrable (fun z:space Ω=>|g (τ,z)|^2) ν:=by
    apply (integrable_const ((2*C)^2)).mono'
      ((hgs.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    exact ae_of_all _ (fun z=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hgb _) 2)
  have hiSample(τ v:ℝ):Integrable (fun z:Ω×HeatCircle=>|g (τ,((v,z.1),z.2))|^2) (μ.prod haarAddCircle):=by
    have hm:Measurable (fun z:Ω×HeatCircle=>(τ,((v,z.1),z.2))):=
      measurable_const.prodMk ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
    apply (integrable_const ((2*C)^2)).mono' ((hgs.comp hm).aestronglyMeasurable)
    exact ae_of_all _ (fun z=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hgb _) 2)
  have heq(τ:ℝ)(hτ:τ∈Ioo (0:ℝ) h):
      rowEnergy μ P U V Λ a j W h τ=∫z:space Ω,|g (τ,z)|^2 ∂ν:=by
    rw [integral_prod _ (hiSection τ),integral_prod _ ((hiSection τ).integral_prod_left)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    have hc:v+h≤H:=by linarith [hv.2,hcover]
    have he:=NativeJointRowClock.energy_eq 𝓕 μ P U V hU hV Λ H ha hA hholder j hv.1 hc hτ
    rw [he]
    change (∫z:Ω×HeatCircle,|g (τ,((v,z.1),z.2))|^2 ∂μ.prod haarAddCircle)=_
    exact integral_prod _ (hiSample τ v)
  have hmem:∀ᵐτ∂volume.restrict (Ioc (0:ℝ) h),τ∈Ioo (0:ℝ) h:=by
    rw [←restrict_Ioo_eq_restrict_Ioc]
    exact ae_restrict_mem measurableSet_Ioo
  have hfun:(fun τ=>τ^(ρ-1/2)*rowEnergy μ P U V Λ a j W h τ)=ᵐ[volume.restrict (Ioc (0:ℝ) h)]
      (fun τ=>τ^(ρ-1/2)*(∫z:space Ω,|g (τ,z)|^2 ∂ν)):=by
    filter_upwards [hmem] with τ hτ
    rw [heq τ hτ]
  have hb:=NativeMovingJointGamma.energy μ P Ur Dr hUr hDr hDE.1 hΛ hh hh1 hW hW1 hρ0 hρ1 ha hA hholder 0 j
  refine ⟨hb.1.congr hfun.symm,?_⟩
  rw [integral_congr_ae hfun]
  have hdEq:(∫z,‖Dr z‖^2 ∂((volume:Measure ℝ).prod μ))=
      ∫z,‖V z-U z‖^2 ∂((PredictableL2.timeMeasure H).prod μ):=hDE.2
  rw [hdEq] at hb
  exact hb.2
end SHE.NativeJointRowTime
