module
public import SHE.MixedNativeEnvelopeIntegral

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.MixedNativeInitialEnvelopeIntegral
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation Real
  ControlledProfile ControlledReferenceLevel ControlledOldIntervals NativeSignedHaarProcess PhysicalScoreChain
  SmoothCylinders UniformSmooth CutoffWordLevel
open scoped NNReal ENNReal
local instance mixedNativeInitialEnvelopeIntegral_realSigma:MeasurableSpace RealL2:=borel _
local instance mixedNativeInitialEnvelopeIntegral_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance mixedNativeInitialEnvelopeIntegral_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance mixedNativeInitialEnvelopeIntegral_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
local instance mixedNativeInitialEnvelopeIntegral_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance mixedNativeInitialEnvelopeIntegral_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z∧aU z≤M)(hbV:∀z,ell≤aV z∧aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (P:CanonicalCovariance.ProfileParameters)
local notation "CU"=>ContinuousHeatMild.coefficientFunction haU hell hbU S.first
local notation "CV"=>ContinuousHeatMild.coefficientFunction haV hell hbV S.second


open Set
local notation "Env"=>MovingNativeFourTermEnergy.envelope 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P
local notation "Fcur"=>MixedMovingEnergy.ennEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Fneg"=>MixedNativeInputEnergyClock.ennEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S


private theorem four {α β:Type*}[MeasurableSpace α][MeasurableSpace β]
    (μα:Measure α)(νβ:Measure β)[SFinite μα][SFinite νβ]
    (f₁ f₂ f₃ f₄:α×β→ℝ≥0∞)(hf₁:Measurable f₁)(hf₂:Measurable f₂)
    (hf₃:Measurable f₃)(hf₄:Measurable f₄)(a b c d:ℝ≥0∞):
    (∫⁻x,∫⁻y,a*f₁ (x,y)+b*f₂ (x,y)+c*f₃ (x,y)+d*f₄ (x,y) ∂νβ ∂μα)=
      a*(∫⁻x,∫⁻y,f₁ (x,y) ∂νβ ∂μα)+b*(∫⁻x,∫⁻y,f₂ (x,y) ∂νβ ∂μα)+
      c*(∫⁻x,∫⁻y,f₃ (x,y) ∂νβ ∂μα)+d*(∫⁻x,∫⁻y,f₄ (x,y) ∂νβ ∂μα):=by
  have h₁:=hf₁.const_mul a
  have h₂:=hf₂.const_mul b
  have h₃:=hf₃.const_mul c
  have h₄:=hf₄.const_mul d
  have h₁₂:Measurable (fun z=>a*f₁ z+b*f₂ z):=h₁.add h₂
  have h₁₂₃:Measurable (fun z=>a*f₁ z+b*f₂ z+c*f₃ z):=h₁₂.add h₃
  calc
    _=∫⁻z,a*f₁ z+b*f₂ z+c*f₃ z+d*f₄ z ∂μα.prod νβ:=
      (lintegral_prod _ (((h₁.add h₂).add h₃).add h₄).aemeasurable).symm
    _=a*(∫⁻z,f₁ z ∂μα.prod νβ)+b*(∫⁻z,f₂ z ∂μα.prod νβ)+
        c*(∫⁻z,f₃ z ∂μα.prod νβ)+d*(∫⁻z,f₄ z ∂μα.prod νβ):=by
      rw [lintegral_add_left h₁₂₃,lintegral_add_left h₁₂,
        lintegral_add_left h₁,lintegral_const_mul a hf₁,lintegral_const_mul b hf₂,
        lintegral_const_mul c hf₃,lintegral_const_mul d hf₄]
    _=_:=by
      rw [lintegral_prod _ hf₁.aemeasurable,lintegral_prod _ hf₂.aemeasurable,
        lintegral_prod _ hf₃.aemeasurable,lintegral_prod _ hf₄.aemeasurable]



private theorem triangle_four (μt:Measure ℝ)[SFinite μt]
    (f₁ f₂ f₃ f₄:ℝ×ℝ→ℝ≥0∞)(hf₁:Measurable f₁)(hf₂:Measurable f₂)
    (hf₃:Measurable f₃)(hf₄:Measurable f₄)(a b c d:ℝ≥0∞):
    (∫⁻t,∫⁻q in Ioc (0:ℝ) t,a*f₁ (t,q)+b*f₂ (t,q)+c*f₃ (t,q)+d*f₄ (t,q) ∂volume ∂μt)=
      a*(∫⁻t,∫⁻q in Ioc (0:ℝ) t,f₁ (t,q) ∂volume ∂μt)+b*(∫⁻t,∫⁻q in Ioc (0:ℝ) t,f₂ (t,q) ∂volume ∂μt)+
      c*(∫⁻t,∫⁻q in Ioc (0:ℝ) t,f₃ (t,q) ∂volume ∂μt)+d*(∫⁻t,∫⁻q in Ioc (0:ℝ) t,f₄ (t,q) ∂volume ∂μt):=by
  let D:Set (ℝ×ℝ):={z|0<z.2 ∧ z.2≤z.1}
  have hDm:MeasurableSet D:=(measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd measurable_fst)
  let g₁:=D.indicator f₁
  let g₂:=D.indicator f₂
  let g₃:=D.indicator f₃
  let g₄:=D.indicator f₄
  have hi(f:ℝ×ℝ→ℝ≥0∞)(t:ℝ):
      (∫⁻q,D.indicator f (t,q))=∫⁻q in Ioc (0:ℝ) t,f (t,q):=by
    change (∫⁻q,(Ioc (0:ℝ) t).indicator (fun q=>f (t,q)) q)=_
    exact lintegral_indicator measurableSet_Ioc _
  have he(t:ℝ):
      (∫⁻q in Ioc (0:ℝ) t,a*f₁ (t,q)+b*f₂ (t,q)+c*f₃ (t,q)+d*f₄ (t,q))=
      ∫⁻q,a*g₁ (t,q)+b*g₂ (t,q)+c*g₃ (t,q)+d*g₄ (t,q):=by
    rw [←lintegral_indicator measurableSet_Ioc]
    apply lintegral_congr
    intro q
    by_cases hq:q∈Ioc (0:ℝ) t
    · have hDq:(t,q)∈D:=hq
      simp only [g₁,g₂,g₃,g₄,Set.indicator_of_mem hq,Set.indicator_of_mem hDq]
    · have hDq:(t,q)∉D:=hq
      simp only [g₁,g₂,g₃,g₄,Set.indicator_of_notMem hq,Set.indicator_of_notMem hDq,mul_zero,add_zero]
  calc
    _=∫⁻t,∫⁻q,a*g₁ (t,q)+b*g₂ (t,q)+c*g₃ (t,q)+d*g₄ (t,q) ∂volume ∂μt:=
      lintegral_congr_ae (ae_of_all _ he)
    _=a*(∫⁻t,∫⁻q,g₁ (t,q) ∂volume ∂μt)+b*(∫⁻t,∫⁻q,g₂ (t,q) ∂volume ∂μt)+
      c*(∫⁻t,∫⁻q,g₃ (t,q) ∂volume ∂μt)+d*(∫⁻t,∫⁻q,g₄ (t,q) ∂volume ∂μt):=
      four μt volume g₁ g₂ g₃ g₄ (hf₁.indicator hDm) (hf₂.indicator hDm)
        (hf₃.indicator hDm) (hf₄.indicator hDm) a b c d
    _=_:=by simp only [g₁,g₂,g₃,g₄,hi]


/-- The initial triangle is integrated on its true variable-terminal
old cube. The common initial data remove the past-energy term exactly. -/
theorem initial (k:ℕ)(A ν ρ χ ε tail η:ℝ)(hν:1≤ν)(hΛ:1≤Λ)(hρ:0<ρ)(hρhalf:ρ<1/2)(hχ:0≤χ)
    (p:ℕ)(Bcur Bword:ℝ≥0):
    let h:=NativeBandFrequencyRates.window P.exponent ν
    let Cf:=NativeUniversalConstants.rowConstant (1+k)
    let Cdim:=NativeUniversalConstants.currentConstant.{0} (1+k) (by omega)
    let C:=MixedPastNativeQuarterRMS.coefficient κ (M:=M) P k Cf ρ
    let Ccur:=sqrt (8*C*MixedPastNativeEnergyNormalization.currentCoefficient κ (M:=M) P k p χ Cdim Bcur)
    let Jt:=MixedPastSignedEndpointMoments.traceConstant (Ω:=Ω) (M:=M) hell ρ hρ hρhalf
    let Cmom:=MixedPastWordMoments.momentConstant P k k p
      ((k:ℝ)*(NativeHybridMoments.momentConstant (p*(k+2)) Bcur κ M)^P.exponent)
    let Cgood:=PastSignedEndpointTime.goodCoefficient P k Jt ρ η
    let Cbad:=PastSignedEndpointTime.badCoefficient P k M Cmom
    let G:=fun r a t q=>ENNReal.ofReal (NativeCurrentBudgetFrequency.majorant P (fraction P*P.lower) (uniformConstant 1) k r a ν (t-q)^2)
    (∫⁻t in Ioc (0:ℝ) (min (H:ℝ) h),∫⁻q in Ioc (0:ℝ) t,
      ENNReal.ofReal (Env 0 t.toNNReal q.toNNReal k (A*ν^(-P.exponent)) ν Λ ρ χ ν ε tail η hΛ hρ hρhalf p Bcur Bword))=
    ENNReal.ofReal (8*A^2*Ccur^2)*(ENNReal.ofReal (ν^(-2*P.exponent))*
      (∫⁻t in Ioc (0:ℝ) (min (H:ℝ) h),∫⁻q in Ioc (0:ℝ) t,G ρ χ t q*Fcur q^χ))+
    ENNReal.ofReal (4*A^2*Cgood^2)*(ENNReal.ofReal (ν^(-2*P.exponent+2*ε))*
      (∫⁻t in Ioc (0:ℝ) (min (H:ℝ) h),∫⁻q in Ioc (0:ℝ) t,G (ρ+η) (2*(ρ+η)) t q*Fneg hΛ hρ.le q))+
    ENNReal.ofReal (4*A^2*Cbad^2)*(ENNReal.ofReal (ν^(-2*P.exponent-tail))*
      (∫⁻t in Ioc (0:ℝ) (min (H:ℝ) h),∫⁻q in Ioc (0:ℝ) t,G 0 0 t q)):=by
  intro h Cf Cdim C Ccur Jt Cmom Cgood Cbad G
  let f₁:ℝ×ℝ→ℝ≥0∞:=fun z=>G ρ χ z.1 z.2*Fcur z.2^χ
  let f₂:ℝ×ℝ→ℝ≥0∞:=fun _=>0
  let f₃:ℝ×ℝ→ℝ≥0∞:=fun z=>G (ρ+η) (2*(ρ+η)) z.1 z.2*Fneg hΛ hρ.le z.2
  let f₄:ℝ×ℝ→ℝ≥0∞:=fun z=>G 0 0 z.1 z.2
  have hG(r a:ℝ):Measurable (fun z:ℝ×ℝ=>G r a z.1 z.2):=ENNReal.measurable_ofReal.comp
    (((NativeCurrentBudgetFrequency.majorant_measurable P (fraction P*P.lower) (uniformConstant 1) k r a ν).comp
      (measurable_fst.sub measurable_snd)).pow_const 2)
  have hFc:=MixedMovingEnergy.ennEnergy_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  have hFn:=MixedNativeInputEnergyClock.ennEnergy_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hΛ hρ.le
  have hf₁:Measurable f₁:=(hG ρ χ).mul ((hFc.comp measurable_snd).pow_const χ)
  have hf₂:Measurable f₂:=measurable_const
  have hf₃:Measurable f₃:=(hG (ρ+η) (2*(ρ+η))).mul (hFn.comp measurable_snd)
  have hf₄:Measurable f₄:=hG 0 0
  let a:=ENNReal.ofReal (8*A^2*Ccur^2)*ENNReal.ofReal (ν^(-2*P.exponent))
  let c:=ENNReal.ofReal (4*A^2*Cgood^2)*ENNReal.ofReal (ν^(-2*P.exponent+2*ε))
  let d:=ENNReal.ofReal (4*A^2*Cbad^2)*ENNReal.ofReal (ν^(-2*P.exponent-tail))
  have hF0:Fcur (0:ℝ)=0:=by
    simp only [MixedMovingEnergy.ennEnergy,MixedMovingEnergy.realEnergy,
      Set.indicator_of_notMem (show (0:ℝ)∉Ioc 0 (H:ℝ) by simp),ENNReal.ofReal_zero]
  have he:(∫⁻t in Ioc (0:ℝ) (min (H:ℝ) h),∫⁻q in Ioc (0:ℝ) t,
      ENNReal.ofReal (Env 0 t.toNNReal q.toNNReal k (A*ν^(-P.exponent)) ν Λ ρ χ ν ε tail η hΛ hρ hρhalf p Bcur Bword))=
      ∫⁻t in Ioc (0:ℝ) (min (H:ℝ) h),∫⁻q in Ioc (0:ℝ) t,
        a*f₁ (t,q)+0*f₂ (t,q)+c*f₃ (t,q)+d*f₄ (t,q):=by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [←Measure.restrict_congr_set (Ioo_ae_eq_Ioc:Ioo (0:ℝ) t=ᵐ[volume] Ioc 0 t)]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
    have ht':(t.toNNReal:ℝ)=t:=Real.coe_toNNReal _ ht.1.le
    have hq':(q.toNNReal:ℝ)=q:=Real.coe_toNNReal _ hq.1.le
    have hq0:0<q.toNNReal:=Real.toNNReal_pos.mpr hq.1
    have hqt:q.toNNReal<t.toNNReal:=by
      apply NNReal.coe_lt_coe.mp
      simpa only [hq',ht'] using hq.2
    have htH:(0:ℝ≥0)+t.toNNReal≤H:=by
      apply NNReal.coe_le_coe.mp
      simpa only [zero_add,ht'] using ht.2.trans (min_le_left _ _)
    have hp:=MixedNativeEnvelopeClock.completed
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P
      0 t.toNNReal q.toNNReal hq0 hqt htH k A ν ρ χ ε tail η hν hΛ hρ hρhalf hχ p Bcur Bword
    simp only [NNReal.coe_add,NNReal.coe_zero,zero_add,hq',ht',hF0,mul_zero,add_zero] at hp
    simpa only [a,c,d,f₁,f₂,f₃,f₄,Cf,Cdim,C,Ccur,Jt,Cmom,Cgood,Cbad,G,mul_assoc,zero_mul,add_zero] using hp
  rw [he]
  simpa only [a,c,d,f₁,f₂,f₃,f₄,mul_assoc,zero_mul,add_zero] using
    triangle_four (volume.restrict (Ioc (0:ℝ) (min (H:ℝ) h))) f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄ a 0 c d

end SHE.MixedNativeInitialEnvelopeIntegral
