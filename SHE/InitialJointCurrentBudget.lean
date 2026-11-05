module
public import SHE.InitialJointGradientClock
public import SHE.NativeRowEnergyCast
public import SHE.MovingClockEnergy
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
namespace SHE.InitialJointCurrentBudget
open Set MeasureTheory PredictableL2 Real AddCircle StoppedFourier NativeHeatObservation NativeMovingCurrentGamma ScalarGaussianSemigroup DyadicApproximation
open scoped NNReal ENNReal
local instance : Fact (0<2*π):=⟨by positivity⟩
local instance : MeasurableSpace RealL2:=borel _
local instance : BorelSpace RealL2:=⟨rfl⟩
local instance : MeasurableSpace CircleL2:=borel _
local instance : BorelSpace CircleL2:=⟨rfl⟩
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2:=FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
variable {Ω:Type*} [MeasurableSpace Ω]

/-- Initial terminal-time integration is carried out BEFORE clipping.
This is the actual native current row on the strict physical triangle;
the original path energy is retained, with no supplied current budget. -/
theorem energy_measurable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω)[IsProbabilityMeasure μ]
    (P:CanonicalCovariance.ProfileParameters) (H:ℝ≥0) (U V:ℝ≥0×Ω→RealL2)
    (hU:StronglyMeasurable[𝓕.predictable] U) (hV:StronglyMeasurable[𝓕.predictable] V)
    (hi:Integrable (fun z=>‖V z-U z‖^2) ((timeMeasure H).prod μ))
    {Λ h ρ A:ℝ}(hΛ:0≤Λ) (hh:0<h) (hh1:h≤1) (hρ0:-(1/2:ℝ)<ρ) (hρ1:ρ<1/2)
    {a:ℝ→ℝ}(ha:SmoothCylinders.BoundedSmooth a) (hA:0≤A)
    (hholder:∀x y,|a x-a y|≤A*|x-y|^P.exponent) (j:ℕ):
    (∫⁻T in Ioc (0:ℝ) (min (H:ℝ) h),∫⁻τ in Ioc (0:ℝ) T,∫⁻ω,ENNReal.ofReal
      (τ^(ρ-1/2)*‖NativeRandomRows.nativeRow
        (NativeJointRowClock.field P U V Λ 0 T.toNNReal a j 0) ((T-τ).toNNReal,ω)-
          NativeRandomRows.nativeRow (NativeJointRowClock.field P U V Λ 0 T.toNNReal a j 1)
            ((T-τ).toNNReal,ω)‖^2) ∂μ)≤
      ENNReal.ofReal ((2*A*ScalarHeatGradientDifference.constant P.exponent)^2*
        ScalarHeatBandTime.massConstant P.exponent ρ*(ProfileVariance.lowerConstant*P.lower)^(-1-2*ρ)*
          CompactMollifier.radius (j+1)^(2*P.exponent+4*ρ)*
            min 1 ((4*∫z,‖V z-U z‖^2 ∂((timeMeasure H).prod μ))/CompactMollifier.radius (j+1)^2))∧ AEMeasurable (fun T:ℝ=>∫⁻τ in Ioc (0:ℝ) T,∫⁻ω,ENNReal.ofReal
      (τ^(ρ-1/2)*‖NativeRandomRows.nativeRow
        (NativeJointRowClock.field P U V Λ 0 T.toNNReal a j 0) ((T-τ).toNNReal,ω)-
          NativeRandomRows.nativeRow (NativeJointRowClock.field P U V Λ 0 T.toNNReal a j 1)
            ((T-τ).toNNReal,ω)‖^2) ∂μ) (volume.restrict (Ioc (0:ℝ) (min (H:ℝ) h))):=by
  let Ur:=fun z:ℝ×Ω=>U (z.1.toNNReal,z.2)
  let Dr:=NativePathZeroExtension.extend H (fun p=>V p-U p)
  let past:=InitialJointGradientClock.past U V
  have hmU:Measurable U:=(hU.mono (predictable_le_product 𝓕)).measurable
  have hmV:Measurable V:=(hV.mono (predictable_le_product 𝓕)).measurable
  have hUr:Measurable Ur:=hmU.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hDr:Measurable Dr:=NativePathZeroExtension.measurable H _ (hmV.sub hmU)
  have hp:Measurable past:=by
    exact ((embed.continuous.measurable.comp (hmU.comp (measurable_const.prodMk measurable_id))).prodMk
      (embed.continuous.measurable.comp ((hmV.sub hmU).comp (measurable_const.prodMk measurable_id))))
  have hDE:=NativePathZeroExtension.energy μ H (fun z=>V z-U z) (hmV.sub hmU) hi
  let ν:=((volume.restrict (Ioc (-h) (0:ℝ))).prod μ).prod (haarAddCircle (T:=2*π))
  let σ:=InitialJointGradientEnergy.variance P Λ h past
  let x:=current Ur h
  let y:=fun p=>x p+NativeMovingJointGamma.direction Dr Λ h p
  let g:=fun p=>deriv (heat (σ p).toNNReal (ScalarHeatBands.band a (j+1))) (y p)-
    deriv (heat (σ p).toNNReal (ScalarHeatBands.band a (j+1))) (x p)
  have hs:Measurable σ:=InitialJointGradientEnergy.variance_measurable P Λ h past hp
  have hx:Measurable x:=current_measurable Ur hUr h
  have hy:Measurable y:=hx.add (NativeMovingJointGamma.direction_measurable Dr hDr Λ h)
  have hg:Measurable g:=(PolynomialGaussianDecay.derivative_measurable ha (j+1) σ y hs hy).sub
    (PolynomialGaussianDecay.derivative_measurable ha (j+1) σ x hs hx)
  have hgs:Measurable (fun p=>|g p|^2):=by simpa only [Real.norm_eq_abs] using hg.norm.pow_const 2
  let C:=ScalarHeatSingleMultiplier.cap A P.exponent j
  have hgb(p:ℝ×space Ω):|g p|≤2*C:=by
    have hb(t:ℝ):|deriv (heat (σ p).toNNReal (ScalarHeatBands.band a (j+1))) t|≤C:=by
      simpa only [C,ScalarHeatSingleMultiplier.cap,iteratedDeriv_one,Nat.zero_add,Nat.cast_zero,sub_zero] using
        ScalarHeatBandJets.heated_positive_jet ha hA P.exponent_pos.le P.exponent_le_one hholder (σ p).toNNReal (j+1) 0 t
    exact (abs_sub _ _).trans ((add_le_add (hb _) (hb _)).trans_eq (by ring))
  have hiSection(τ:ℝ):Integrable (fun z:space Ω=>|g (τ,z)|^2) ν:=by
    apply (integrable_const ((2*C)^2)).mono' ((hgs.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    exact ae_of_all _ (fun z=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hgb _) 2)
  let f:ℝ×ℝ→ℝ≥0∞:=fun p=>∫⁻ω,∫⁻x,ENNReal.ofReal (p.1^(ρ-1/2)*|g (p.1,((p.2,ω),x))|^2) ∂haarAddCircle ∂μ
  have hfm:Measurable f:=by
    have hm:Measurable (fun p:((ℝ×ℝ)×Ω)×HeatCircle=>ENNReal.ofReal
        (p.1.1.1^(ρ-1/2)*|g (p.1.1.1,((p.1.1.2,p.1.2),p.2))|^2)):=by
      exact ((by fun_prop:Measurable (fun p:((ℝ×ℝ)×Ω)×HeatCircle=>p.1.1.1^(ρ-1/2))).mul
        (hgs.comp (measurable_fst.fst.fst.prodMk ((measurable_fst.fst.snd.prodMk measurable_fst.snd).prodMk measurable_snd)))).ennreal_ofReal
    exact hm.lintegral_prod_right.lintegral_prod_right
  have hb:=InitialJointGradientEnergy.energy μ P Ur Dr hUr hDr hDE.1 past hp hΛ hh hh1 hρ0 hρ1 ha hA hholder j
  have hrect:(∫⁻τ in Ioc (0:ℝ) h,∫⁻v in Ioc (-h) (0:ℝ),f (τ,v))≤
      ENNReal.ofReal ((2*A*ScalarHeatGradientDifference.constant P.exponent)^2*
        ScalarHeatBandTime.massConstant P.exponent ρ*(ProfileVariance.lowerConstant*P.lower)^(-1-2*ρ)*
          CompactMollifier.radius (j+1)^(2*P.exponent+4*ρ)*
            min 1 ((4*∫z,‖V z-U z‖^2 ∂((timeMeasure H).prod μ))/CompactMollifier.radius (j+1)^2)):=by
    calc
      _=(∫⁻τ in Ioc (0:ℝ) h,∫⁻z,ENNReal.ofReal (τ^(ρ-1/2)*|g (τ,z)|^2) ∂ν):=by
        apply lintegral_congr
        intro τ
        have hmt:Measurable (fun z:space Ω=>ENNReal.ofReal (τ^(ρ-1/2)*|g (τ,z)|^2)):=
          (((by fun_prop:Measurable (fun z:space Ω=>τ^(ρ-1/2))).mul
            (hgs.comp (measurable_const.prodMk measurable_id))).ennreal_ofReal)
        rw [lintegral_prod _ hmt.aemeasurable,lintegral_prod _ hmt.lintegral_prod_right.aemeasurable]
      _=ENNReal.ofReal (∫τ in Ioc (0:ℝ) h,τ^(ρ-1/2)*(∫z,|g (τ,z)|^2 ∂ν)):=by
        rw [ofReal_integral_eq_lintegral_ofReal hb.1]
        · apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ ht
          rw [←ofReal_integral_eq_lintegral_ofReal ((hiSection τ).const_mul _)
            (ae_of_all _ (fun _=>mul_nonneg (rpow_nonneg ht.1.le _) (sq_nonneg _))),integral_const_mul]
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ ht
          exact mul_nonneg (rpow_nonneg ht.1.le _) (integral_nonneg (fun _=>sq_nonneg _))
      _≤ENNReal.ofReal ((2*A*ScalarHeatGradientDifference.constant P.exponent)^2*
        ScalarHeatBandTime.massConstant P.exponent ρ*(ProfileVariance.lowerConstant*P.lower)^(-1-2*ρ)*
          CompactMollifier.radius (j+1)^(2*P.exponent+4*ρ)*
            min 1 ((4*∫z,‖V z-U z‖^2 ∂((timeMeasure H).prod μ))/CompactMollifier.radius (j+1)^2)):=by
        apply ENNReal.ofReal_le_ofReal
        have he:(∫z,‖Dr z‖^2 ∂((volume:Measure ℝ).prod μ))=(∫z,‖V z-U z‖^2 ∂((timeMeasure H).prod μ)):=hDE.2
        have hr:=hb.2
        change (∫τ in Ioc (0:ℝ) h,τ^(ρ-1/2)*(∫z,|g (τ,z)|^2 ∂ν))≤_ at hr
        rw [he] at hr
        exact hr
  have hpoint(T:ℝ) (hT:T∈Ioc (0:ℝ) (min (H:ℝ) h)) (τ:ℝ) (hτ:τ∈Ioo (0:ℝ) T):
      (∫⁻ω,ENNReal.ofReal (τ^(ρ-1/2)*‖NativeRandomRows.nativeRow
        (NativeJointRowClock.field P U V Λ 0 T.toNNReal a j 0) ((T-τ).toNNReal,ω)-
          NativeRandomRows.nativeRow (NativeJointRowClock.field P U V Λ 0 T.toNNReal a j 1)
            ((T-τ).toNNReal,ω)‖^2) ∂μ)=f (τ,T-h):=by
    apply lintegral_congr
    intro ω
    let F0:=NativeJointRowClock.field P U V Λ 0 T.toNNReal a j 0
    let F1:=NativeJointRowClock.field P U V Λ 0 T.toNNReal a j 1
    have hm0:=NativeJointRowClock.field_measurable 𝓕 P U V hU hV Λ 0 T.toNNReal ha j 0
    have hm1:=NativeJointRowClock.field_measurable 𝓕 P U V hU hV Λ 0 T.toNNReal ha j 1
    have he:=ScalarHeatPairedMultipliers.difference_norm ha hA P.exponent_pos.le P.exponent_le_one hholder j
      (show Measurable (NativeJointRowClock.variance P U V Λ 0 T.toNNReal) from
        (NativeJointGammaFields.variance_predictable (𝓕:=𝓕) (v:=0) (b:=T.toNNReal) (U:=U) (V:=V) (hU:=hU) (hV:=hV) (P:=P) (Λ:=Λ) 0).comp
          ((measurable_id'' (predictable_le_product 𝓕)).prodMap measurable_id))
      (show Measurable (NativeJointRowClock.variance P U V Λ 0 T.toNNReal) from
        (NativeJointGammaFields.variance_predictable (𝓕:=𝓕) (v:=0) (b:=T.toNNReal) (U:=U) (V:=V) (hU:=hU) (hV:=hV) (P:=P) (Λ:=Λ) 0).comp
          ((measurable_id'' (predictable_le_product 𝓕)).prodMap measurable_id))
      (show Measurable (NativeJointRowClock.mean U V Λ 0 0 T.toNNReal) from
        (NativeJointGammaFields.current_predictable (𝓕:=𝓕) (v:=0) (b:=T.toNNReal) (U:=U) (V:=V) (hU:=hU) (hV:=hV) (Λ:=Λ) 0).comp
          ((measurable_id'' (predictable_le_product 𝓕)).prodMap measurable_id))
      (show Measurable (NativeJointRowClock.mean U V Λ 1 0 T.toNNReal) from
        (NativeJointGammaFields.current_predictable (𝓕:=𝓕) (v:=0) (b:=T.toNNReal) (U:=U) (V:=V) (hU:=hU) (hV:=hV) (Λ:=Λ) 1).comp
          ((measurable_id'' (predictable_le_product 𝓕)).prodMap measurable_id)) ((T-τ).toNNReal,ω)
    change ENNReal.ofReal (τ^(ρ-1/2)*‖ScalarHeatSingleMultiplier.multiplier a j _ _ _-
      ScalarHeatSingleMultiplier.multiplier a j _ _ _‖^2)=_
    rw [he]
    dsimp only [NativeJointRowClock.variance,NativeJointRowClock.mean]
    rw [integral_congr_ae (InitialJointGradientClock.gradient_ae P U V Λ H a j hT.1
      ((hT.2.trans (min_le_right _ _)).trans hh1) (hT.2.trans (min_le_left _ _)) hτ ω)]
    have hgi:Integrable (fun x:HeatCircle=>|g (τ,(((T-h,ω),x)))|^2) haarAddCircle:=by
      apply (integrable_const ((2*C)^2)).mono'
        ((hgs.comp (measurable_const.prodMk ((measurable_const.prodMk measurable_const).prodMk measurable_id))).aestronglyMeasurable)
      exact ae_of_all _ (fun x=>by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hgb _) 2)
    change ENNReal.ofReal (τ^(ρ-1/2)*(∫x:HeatCircle,|g (τ,(((T-h,ω),x)))|^2 ∂haarAddCircle))=_
    rw [←integral_const_mul]
    exact ofReal_integral_eq_lintegral_ofReal (hgi.const_mul _)
      (ae_of_all _ (fun _=>mul_nonneg (rpow_nonneg hτ.1.le _) (sq_nonneg _)))
  refine ⟨?_,?_⟩
  ·
    calc
      _=(∫⁻T in Ioc (0:ℝ) (min (H:ℝ) h),∫⁻τ in Ioc (0:ℝ) T,f (τ,T-h)):=by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with T hT
        apply lintegral_congr_ae
        have hmem:∀ᵐτ∂volume.restrict (Ioc (0:ℝ) T),τ∈Ioo (0:ℝ) T:=by
          rw [←restrict_Ioo_eq_restrict_Ioc]
          exact ae_restrict_mem measurableSet_Ioo
        filter_upwards [hmem] with τ hτ
        exact hpoint T hT τ hτ
      _≤∫⁻T in Ioc (0:ℝ) (min (H:ℝ) h),∫⁻τ in Ioc (0:ℝ) h,f (τ,T-h):=by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with T hT
        exact lintegral_mono_set (Ioc_subset_Ioc_right (hT.2.trans (min_le_right _ _)))
      _≤∫⁻T in Ioc (0:ℝ) h,∫⁻τ in Ioc (0:ℝ) h,f (τ,T-h):=
        lintegral_mono_set (Ioc_subset_Ioc_right (min_le_right _ _))
      _=(∫⁻v in Ioc (-h) (0:ℝ),∫⁻τ in Ioc (0:ℝ) h,f (τ,v)):=by
        have ht:=(MovingClockEnergy.translation (-h) h).lintegral_comp_emb
          (MeasurableEquiv.addRight (-h)).measurableEmbedding (fun v=>∫⁻τ in Ioc (0:ℝ) h,f (τ,v))
        simpa only [neg_add_cancel,MeasurableEquiv.coe_addRight,←sub_eq_add_neg] using ht
      _=(∫⁻τ in Ioc (0:ℝ) h,∫⁻v in Ioc (-h) (0:ℝ),f (τ,v)):=by
        exact lintegral_lintegral_swap (hfm.comp measurable_swap).aemeasurable
      _≤_:=hrect
  · let f0:ℝ×ℝ→ℝ≥0∞:=fun p=>if 0<p.2∧p.2≤p.1 then f (p.2,p.1-h) else 0
    have hf0:Measurable f0:=(hfm.comp (measurable_snd.prodMk (measurable_fst.sub_const h))).ite
      ((measurableSet_lt measurable_const measurable_snd).inter (measurableSet_le measurable_snd measurable_fst)) measurable_const
    have he(T:ℝ):(∫⁻τ,f0 (T,τ))=∫⁻τ in Ioc (0:ℝ) T,f (τ,T-h):=by
      rw [←lintegral_indicator measurableSet_Ioc]
      apply lintegral_congr
      intro τ
      by_cases ht:τ∈Ioc (0:ℝ) T
      · rw [indicator_of_mem ht]
        exact if_pos ht
      · rw [indicator_of_notMem ht]
        exact if_neg ht
    have hmInt:Measurable (fun T:ℝ=>∫⁻τ:ℝ,f0 (T,τ)):=hf0.lintegral_prod_right
    refine hmInt.aemeasurable.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with T hT
    rw [he]
    apply lintegral_congr_ae
    have hm:∀ᵐτ∂volume.restrict (Ioc (0:ℝ) T),τ∈Ioo (0:ℝ) T:=by
      rw [←restrict_Ioo_eq_restrict_Ioc]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [hm] with τ hτ
    exact (hpoint T hT τ hτ).symm

theorem energy (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω)[IsProbabilityMeasure μ]
    (P:CanonicalCovariance.ProfileParameters) (H:ℝ≥0) (U V:ℝ≥0×Ω→RealL2)
    (hU:StronglyMeasurable[𝓕.predictable] U) (hV:StronglyMeasurable[𝓕.predictable] V)
    (hi:Integrable (fun z=>‖V z-U z‖^2) ((timeMeasure H).prod μ))
    {Λ h ρ A:ℝ}(hΛ:0≤Λ) (hh:0<h) (hh1:h≤1) (hρ0:-(1/2:ℝ)<ρ) (hρ1:ρ<1/2)
    {a:ℝ→ℝ}(ha:SmoothCylinders.BoundedSmooth a) (hA:0≤A)
    (hholder:∀x y,|a x-a y|≤A*|x-y|^P.exponent) (j:ℕ):
    (∫⁻T in Ioc (0:ℝ) (min (H:ℝ) h),∫⁻τ in Ioc (0:ℝ) T,∫⁻ω,ENNReal.ofReal
      (τ^(ρ-1/2)*‖NativeRandomRows.nativeRow
        (NativeJointRowClock.field P U V Λ 0 T.toNNReal a j 0) ((T-τ).toNNReal,ω)-
          NativeRandomRows.nativeRow (NativeJointRowClock.field P U V Λ 0 T.toNNReal a j 1)
            ((T-τ).toNNReal,ω)‖^2) ∂μ)≤
      ENNReal.ofReal ((2*A*ScalarHeatGradientDifference.constant P.exponent)^2*
        ScalarHeatBandTime.massConstant P.exponent ρ*(ProfileVariance.lowerConstant*P.lower)^(-1-2*ρ)*
          CompactMollifier.radius (j+1)^(2*P.exponent+4*ρ)*
            min 1 ((4*∫z,‖V z-U z‖^2 ∂((timeMeasure H).prod μ))/CompactMollifier.radius (j+1)^2)):=by
  exact (energy_measurable 𝓕 μ P H U V hU hV hi hΛ hh hh1 hρ0 hρ1 ha hA hholder j).1
end SHE.InitialJointCurrentBudget
