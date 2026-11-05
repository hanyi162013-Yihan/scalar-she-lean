module
public import SHE.MixedNativeEnvelopeClock
public import SHE.NativeBandFrequencyRates

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.MixedNativeEnvelopeIntegral
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation Real
  ControlledProfile ControlledReferenceLevel ControlledOldIntervals NativeSignedHaarProcess PhysicalScoreChain
  SmoothCylinders UniformSmooth CutoffWordLevel
open scoped NNReal ENNReal
local instance mixedNativeEnvelopeIntegral_realSigma:MeasurableSpace RealL2:=borel _
local instance mixedNativeEnvelopeIntegral_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance mixedNativeEnvelopeIntegral_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance mixedNativeEnvelopeIntegral_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
local instance mixedNativeEnvelopeIntegral_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance mixedNativeEnvelopeIntegral_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
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


/-- Exact Tonelli decomposition of the actual completed-window cap into
its four original energy clocks. Endpoint removal uses Lebesgue AE
before applying the genuine active-window identity. -/
theorem completed (k:ℕ)(A ν ρ χ ε tail η:ℝ)(hν:1≤ν)(hΛ:1≤Λ)(hρ:0<ρ)(hρhalf:ρ<1/2)(hχ:0≤χ)
    (p:ℕ)(Bcur Bword:ℝ≥0):
    let h:=NativeBandFrequencyRates.window P.exponent ν
    let Cf:=NativeUniversalConstants.rowConstant (1+k)
    let Cdim:=NativeUniversalConstants.currentConstant.{0} (1+k) (by omega)
    let C:=MixedPastNativeQuarterRMS.coefficient κ (M:=M) P k Cf ρ
    let Ccur:=sqrt (8*C*MixedPastNativeEnergyNormalization.currentCoefficient κ (M:=M) P k p χ Cdim Bcur)
    let Cpast:=sqrt (2*C*MixedPastNativeEnergyNormalization.pastCoefficient κ (M:=M) P k Bword)
    let Jt:=MixedPastSignedEndpointMoments.traceConstant (Ω:=Ω) (M:=M) hell ρ hρ hρhalf
    let Cmom:=MixedPastWordMoments.momentConstant P k k p
      ((k:ℝ)*(NativeHybridMoments.momentConstant (p*(k+2)) Bcur κ M)^P.exponent)
    let Cgood:=PastSignedEndpointTime.goodCoefficient P k Jt ρ η
    let Cbad:=PastSignedEndpointTime.badCoefficient P k M Cmom
    let G:=fun r a s=>ENNReal.ofReal (NativeCurrentBudgetFrequency.majorant P (fraction P*P.lower) (uniformConstant 1) k r a ν (h-s)^2)
    (∫⁻v in Set.Ioc (0:ℝ) ((H:ℝ)-h),∫⁻s in Set.Ioc (0:ℝ) h,
      ENNReal.ofReal (Env v.toNNReal h.toNNReal s.toNNReal k (A*ν^(-P.exponent)) ν Λ ρ χ ν ε tail η hΛ hρ hρhalf p Bcur Bword))=
    ENNReal.ofReal (8*A^2*Ccur^2)*(ENNReal.ofReal (ν^(-2*P.exponent))*
      (∫⁻v in Set.Ioc (0:ℝ) ((H:ℝ)-h),∫⁻s in Set.Ioc (0:ℝ) h,G ρ χ s*Fcur (v+s)^χ))+
    ENNReal.ofReal (8*A^2*Cpast^2)*(ENNReal.ofReal (ν^(-2*P.exponent))*
      (∫⁻v in Set.Ioc (0:ℝ) ((H:ℝ)-h),∫⁻s in Set.Ioc (0:ℝ) h,ENNReal.ofReal (s^(-(1/2:ℝ)))*G ρ 0 s*Fcur v))+
    ENNReal.ofReal (4*A^2*Cgood^2)*(ENNReal.ofReal (ν^(-2*P.exponent+2*ε))*
      (∫⁻v in Set.Ioc (0:ℝ) ((H:ℝ)-h),∫⁻s in Set.Ioc (0:ℝ) h,G (ρ+η) (2*(ρ+η)) s*Fneg hΛ hρ.le (v+s)))+
    ENNReal.ofReal (4*A^2*Cbad^2)*(ENNReal.ofReal (ν^(-2*P.exponent-tail))*
      (∫⁻v in Set.Ioc (0:ℝ) ((H:ℝ)-h),∫⁻s in Set.Ioc (0:ℝ) h,G 0 0 s)):=by
  intro h Cf Cdim C Ccur Cpast Jt Cmom Cgood Cbad G
  have hh:0<h:=NativeBandFrequencyRates.window_pos (zero_lt_one.trans_le hν)
  let f₁:ℝ×ℝ→ℝ≥0∞:=fun z=>G ρ χ z.2*Fcur (z.1+z.2)^χ
  let f₂:ℝ×ℝ→ℝ≥0∞:=fun z=>ENNReal.ofReal (z.2^(-(1/2:ℝ)))*G ρ 0 z.2*Fcur z.1
  let f₃:ℝ×ℝ→ℝ≥0∞:=fun z=>G (ρ+η) (2*(ρ+η)) z.2*Fneg hΛ hρ.le (z.1+z.2)
  let f₄:ℝ×ℝ→ℝ≥0∞:=fun z=>G 0 0 z.2
  have hG(r a:ℝ):Measurable (fun z:ℝ×ℝ=>G r a z.2):=ENNReal.measurable_ofReal.comp
    (((NativeCurrentBudgetFrequency.majorant_measurable P (fraction P*P.lower) (uniformConstant 1) k r a ν).comp
      (measurable_const.sub measurable_snd)).pow_const 2)
  have hFc:=MixedMovingEnergy.ennEnergy_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  have hFn:=MixedNativeInputEnergyClock.ennEnergy_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hΛ hρ.le
  have hf₁:Measurable f₁:=(hG ρ χ).mul ((hFc.comp (measurable_fst.add measurable_snd)).pow_const χ)
  have hf₂:Measurable f₂:=((ENNReal.measurable_ofReal.comp (measurable_snd.pow_const (-(1/2:ℝ)))).mul (hG ρ 0)).mul (hFc.comp measurable_fst)
  have hf₃:Measurable f₃:=(hG (ρ+η) (2*(ρ+η))).mul (hFn.comp (measurable_fst.add measurable_snd))
  have hf₄:Measurable f₄:=hG 0 0
  let a:=ENNReal.ofReal (8*A^2*Ccur^2)*ENNReal.ofReal (ν^(-2*P.exponent))
  let b:=ENNReal.ofReal (8*A^2*Cpast^2)*ENNReal.ofReal (ν^(-2*P.exponent))
  let c:=ENNReal.ofReal (4*A^2*Cgood^2)*ENNReal.ofReal (ν^(-2*P.exponent+2*ε))
  let d:=ENNReal.ofReal (4*A^2*Cbad^2)*ENNReal.ofReal (ν^(-2*P.exponent-tail))
  have he:(∫⁻v in Set.Ioc (0:ℝ) ((H:ℝ)-h),∫⁻s in Set.Ioc (0:ℝ) h,
      ENNReal.ofReal (Env v.toNNReal h.toNNReal s.toNNReal k (A*ν^(-P.exponent)) ν Λ ρ χ ν ε tail η hΛ hρ hρhalf p Bcur Bword))=
      ∫⁻v in Set.Ioc (0:ℝ) ((H:ℝ)-h),∫⁻s in Set.Ioc (0:ℝ) h,
        a*f₁ (v,s)+b*f₂ (v,s)+c*f₃ (v,s)+d*f₄ (v,s):=by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    rw [←Measure.restrict_congr_set (Ioo_ae_eq_Ioc:Set.Ioo (0:ℝ) h=ᵐ[volume] Set.Ioc 0 h)]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hv':(v.toNNReal:ℝ)=v:=Real.coe_toNNReal _ hv.1.le
    have hs':(s.toNNReal:ℝ)=s:=Real.coe_toNNReal _ hs.1.le
    have hh':(h.toNNReal:ℝ)=h:=Real.coe_toNNReal _ hh.le
    have hs0:0<s.toNNReal:=Real.toNNReal_pos.mpr hs.1
    have hsh:s.toNNReal<h.toNNReal:=by
      apply NNReal.coe_lt_coe.mp
      simpa only [hs',hh'] using hs.2
    have hvh:v.toNNReal+h.toNNReal≤H:=by
      apply NNReal.coe_le_coe.mp
      simpa only [NNReal.coe_add,hv',hh'] using (show v+h≤(H:ℝ) from by linarith [hv.2])
    have hvh0:=MixedNativeEnvelopeClock.completed
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P
      v.toNNReal h.toNNReal s.toNNReal hs0 hsh hvh k A ν ρ χ ε tail η hν hΛ hρ hρhalf hχ p Bcur Bword
    simp only [NNReal.coe_add,hv',hs',hh',ENNReal.ofReal_mul (Real.rpow_nonneg hs.1.le (-(1/2:ℝ)))] at hvh0
    simpa only [a,b,c,d,f₁,f₂,f₃,f₄,Cf,Cdim,C,Ccur,Cpast,Jt,Cmom,Cgood,Cbad,G,mul_assoc] using hvh0
  rw [he]
  simpa only [a,b,c,d,f₁,f₂,f₃,f₄,mul_assoc] using
    four (volume.restrict (Set.Ioc (0:ℝ) ((H:ℝ)-h))) (volume.restrict (Set.Ioc (0:ℝ) h))
      f₁ f₂ f₃ f₄ hf₁ hf₂ hf₃ hf₄ a b c d

end SHE.MixedNativeEnvelopeIntegral
