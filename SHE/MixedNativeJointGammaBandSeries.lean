module

public import SHE.GammaDyadicNormEnvelope
public import SHE.MixedNativeJointGammaDyadicRMS
public import SHE.MixedNativeJointGammaSharpEnergy
public import SHE.JointGammaActualConstantUniform
public import SHE.GammaDyadicWindowScale
public import SHE.MixedNativeJointRowBudgets
public import SHE.MixedNativeJointGammaIntegral
public import SHE.GammaENNRealCollapse
public import SHE.MixedNativeJointGammaOuter
public import SHE.GammaEnvelopeIntegral
public import SHE.MixedNativeJointEnvelopeEnergy
public import SHE.MixedNativeJointGammaEnvelope
public import SHE.MixedNativeMovingJointBudgets
public import SHE.MixedNativeJointSlotEnvelopes
public import SHE.MixedNativeJointGammaOutput
public import SHE.MixedNativeJointGammaPhysicalBudget
public import SHE.MixedNativeSignedBudget
public import SHE.MixedNativeJointDirectBudget
public import SHE.MixedNativeMovingFrozenFactor
public import SHE.MixedNativePastBudget
public import SHE.GammaBandConstants
public import SHE.NativeMovingGammaClock
public import SHE.MixedMovingEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
namespace SHE.MixedNativeJointGammaBandSeries
open Set MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open Real
open scoped NNReal ENNReal
local instance mixedNativeMovingCurrentGamma_realSigma : MeasurableSpace RealL2:=borel _
local instance mixedNativeMovingCurrentGamma_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance mixedNativeMovingCurrentGamma_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance mixedNativeMovingCurrentGamma_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance mixedNativeMovingCurrentGamma_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance mixedNativeMovingCurrentGamma_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance mixedNativeMovingCurrentGamma_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedNativeMovingCurrentGamma_blockSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedNativeMovingCurrentGamma_blockBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance mixedNativeMovingCurrentGamma_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance mixedNativeMovingCurrentGamma_columnsBorel : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
local instance mixedNativeMovingCurrentGamma_unitPos : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance mixedNativeMovingCurrentGamma_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance mixedNativeMovingCurrentGamma_realSecond : SecondCountableTopology RealL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)



variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hΛ : 0≤Λ) (hH : (H:ℝ)≤1) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower 1 J B)
variable (P:CanonicalCovariance.ProfileParameters) (hκP:κ<P.lower)
variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (Bpast:ℝ≥0)(hBDGpast:StandardTerminalBDGPower 2 J Bpast)
variable (hL:1≤Λ){a:ℝ→ℝ}(ha:SmoothCylinders.BoundedSmooth a){A ρ:ℝ}(hA:0≤A)
variable (hρ:0<ρ)(hρhalf:ρ<1/2)(hholder:∀x y,|a x-a y|≤A*|x-y|^P.exponent)
variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
variable (B0 B1:ℝ≥0)(hBDG0:StandardTerminalBDG16 I₀ B0)(hBDG1:StandardTerminalBDG16 I₁ B1)
variable (Bγ:ℝ≥0)(hBDGγ:StandardTerminalBDG16 J Bγ)
variable (hlocal:StandardTerminalPastLocality I₁)(Bnext:ℝ≥0)(hBDGnext:StandardTerminalBDGPower 1 I₁ Bnext)
variable (J0:ℕ)(hJH:(RemainderBandSpans.span P.exponent (J0+1):ℝ)≤H)
variable (hJP:(RemainderBandSpans.span P.exponent (J0+1):ℝ)≤P.horizon)
local notation "Span" n:max=>(RemainderBandSpans.span P.exponent (J0+n+1):ℝ)
local notation "Neg"=>MixedActualEnergyBridge.negativeEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ρ
local notation "Global"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Cgamma"=>JointGammaConstants.nativeConstant P A κ ell M hell hκP hρ hρhalf Bnext

include hJH in
theorem span_le_H (n:ℕ):Span n≤H:=
  (RemainderBandSpans.span_antitone P.exponent_pos.le (show J0+1≤J0+n+1 by omega)).trans hJH
include hJP in
theorem span_le_profile (n:ℕ):Span n≤P.horizon:=by
  have hs:(RemainderBandSpans.span P.exponent (J0+n+1):ℝ)≤
      (RemainderBandSpans.span P.exponent (J0+1):ℝ):=by
    exact_mod_cast RemainderBandSpans.span_antitone P.exponent_pos.le
      (show J0+1≤J0+n+1 by omega)
  exact hs.trans hJP

/-- Original physical Gamma band energy, at its own actual window. -/
def bandEnergy (n:ℕ):ℝ≥0∞:=
  ∫⁻r in Ioc (0:ℝ) ((H:ℝ)-Span n),MixedNativeJointGammaEnvelope.energy
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
    (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (hκP:=hκP) (hH:=hH)
    (h:=Span n) (W:=(H:ℝ)-Span n)
    (hh:=RemainderBandSpans.span_pos P.exponent (J0+n+1))
    (hW0:=sub_nonneg.mpr (span_le_H (P:=P) (H:=H) J0 hJH n)) (hcover:=by linarith)
    (hL:=hL) (ha:=ha) (hA:=hA) (hρ:=hρ) (hρhalf:=hρhalf) (hholder:=hholder)
    (j:=J0+n) (hnull:=hnull) (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1) r
local notation "Band" n:max=>bandEnergy
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
    (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (hκP:=hκP) (hH:=hH)
    (hL:=hL) (ha:=ha) (hA:=hA) (hρ:=hρ) (hρhalf:=hρhalf) (hholder:=hholder)
    (hnull:=hnull) (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1) (J0:=J0) (hJH:=hJH) n

include hIJ₀ hIJ₁ hΛ hBDG hsmall hBDGpast hJP hBDGγ hlocal hBDGnext in
theorem rms_bound (n:ℕ):sqrt (Band n).toReal≤sqrt Cgamma*(
    ((2:ℝ)^(J0+n+1))^(-P.exponent)*sqrt (Neg).toReal+
    ((2:ℝ)^(J0+n+1))^(-GammaDyadicWindowScale.alpha P.exponent ρ)*
      min 1 (sqrt Global*(2:ℝ)^(J0+n+1))+
    ((2:ℝ)^(J0+n+1))^(-GammaDyadicWindowScale.degree P.exponent ρ)*sqrt Global):=by
  have he:=MixedNativeJointGammaDyadicRMS.rms_bound
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
    (I₁:=I₁) (u₀:=u₀) (S:=S) (J:=J) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁)
    (hΛ:=hΛ) (hH:=hH) (P:=P) (hκP:=hκP) (h:=Span n) (W:=(H:ℝ)-Span n)
    (hh:=RemainderBandSpans.span_pos P.exponent (J0+n+1))
    (hhP:=span_le_profile (P:=P) J0 hJP n)
    (hW0:=sub_nonneg.mpr (span_le_H (P:=P) (H:=H) J0 hJH n)) (hcover:=by linarith)
    (hsmall:=hsmall) (Bpast:=Bpast) (hBDGpast:=hBDGpast) (hL:=hL)
    (ha:=ha) (hA:=hA) (hρ:=hρ) (hρhalf:=hρhalf) (hholder:=hholder) (j:=J0+n)
    (hnull:=hnull) (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1)
    (Bγ:=Bγ) (hBDGγ:=hBDGγ) (hlocal:=hlocal) (Bnext:=Bnext) (hBDGnext:=hBDGnext)
    (B:=B) (hBDG:=hBDG) rfl
  simpa only [bandEnergy] using he

include hIJ₀ hIJ₁ hΛ hBDG hsmall hBDGpast hJP hBDGγ hlocal hBDGnext in
/-- Actual original-driver physical Gamma RMS summation, using the
true h_j and original past measures. No recursion-depth limit occurs. -/
theorem series (hα1:GammaDyadicWindowScale.alpha P.exponent ρ<1)
    (hq:0<GammaDyadicWindowScale.degree P.exponent ρ):
    Summable (fun n=>sqrt (Band n).toReal) ∧
    (∑'n,sqrt (Band n).toReal)≤sqrt Cgamma*(
      StateBands.geometricConstant P.exponent*((2:ℝ)^(J0+1))^(-P.exponent)*sqrt (Neg).toReal+
      StateBands.rootConstant (GammaDyadicWindowScale.alpha P.exponent ρ)*
        (sqrt Global)^(GammaDyadicWindowScale.alpha P.exponent ρ)+
      StateBands.geometricConstant (GammaDyadicWindowScale.degree P.exponent ρ)*
        ((2:ℝ)^(J0+1))^(-GammaDyadicWindowScale.degree P.exponent ρ)*sqrt Global):=by
  have hα0:0<GammaDyadicWindowScale.alpha P.exponent ρ:=by
    unfold GammaDyadicWindowScale.alpha
    linarith [P.exponent_pos]
  have hh(n:ℕ):‖sqrt (Band n).toReal‖≤sqrt Cgamma*(
      ((2:ℝ)^(J0+1+n))^(-P.exponent)*sqrt (Neg).toReal+
      ((2:ℝ)^(J0+1+n))^(-GammaDyadicWindowScale.alpha P.exponent ρ)*
        min 1 (sqrt Global*(2:ℝ)^(J0+1+n))+
      ((2:ℝ)^(J0+1+n))^(-GammaDyadicWindowScale.degree P.exponent ρ)*sqrt Global):=by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sqrt_nonneg _),
      show J0+1+n=J0+n+1 by omega] using
      rms_bound (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
        (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
        (I₁:=I₁) (u₀:=u₀) (S:=S) (J:=J) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁)
        (hΛ:=hΛ) (hH:=hH) (P:=P) (hκP:=hκP) (hsmall:=hsmall) (Bpast:=Bpast)
        (hBDGpast:=hBDGpast) (hL:=hL) (ha:=ha) (hA:=hA) (hρ:=hρ) (hρhalf:=hρhalf)
        (hholder:=hholder) (hnull:=hnull) (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1)
        (Bγ:=Bγ) (hBDGγ:=hBDGγ) (hlocal:=hlocal) (Bnext:=Bnext) (hBDGnext:=hBDGnext)
        (B:=B) (hBDG:=hBDG) (J0:=J0) (hJH:=hJH) (hJP:=hJP) n
  have hs:=GammaDyadicNormEnvelope.sum_bound P.exponent_pos hα0 hα1 hq
    (sqrt_nonneg Cgamma) (sqrt_nonneg (Neg).toReal) (sqrt_nonneg Global)
    (J0+1) (fun n=>sqrt (Band n).toReal) hh
  refine ⟨hs.1,?_⟩
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hs.2)
end SHE.MixedNativeJointGammaBandSeries
