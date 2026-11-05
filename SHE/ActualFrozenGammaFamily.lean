module
import all SHE.FullJointGammaMasterAbsolute
import all SHE.FrozenReferenceFinitePrefixes

public import SHE.FrozenReferenceFinitePrefixes
public import SHE.FrozenReferenceFullIdentity
public import SHE.FullJointGammaMasterAbsolute
public import SHE.FullJointGammaOutput
public import SHE.FullJointGammaMaster
public import SHE.MovingOriginalGammaSeries
public import SHE.GammaFrequencyThreshold
public import SHE.PredictableTime
public import SHE.MovingOriginalGammaBands
public import SHE.HilbertBandTails
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import SHE.MovingOriginalGammaSharp
public import SHE.MixedNativeJointGammaBandSeries
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
namespace SHE.ActualFrozenGammaFamily
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

local instance movingOriginalGammaBands_nativeSigma : MeasurableSpace CircleL2:=borel _
local instance movingOriginalGammaBands_nativeBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance movingOriginalGammaBands_nativeSecond : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local notation "spanH" n:max=>MixedNativeJointGammaBandSeries.span_le_H (P:=P) (H:=H) J0 hJH n
local notation "spanP" n:max=>MixedNativeJointGammaBandSeries.span_le_profile (P:=P) J0 hJP n
local notation "spanPos" n:max=>RemainderBandSpans.span_pos P.exponent (J0+n+1)
local notation "Width" n:max=>(H:ℝ)-Span n
local notation "Band" n:max=>MixedNativeJointGammaBandSeries.bandEnergy
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
    (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (hκP:=hκP) (hH:=hH)
    (hL:=hL) (ha:=ha) (hA:=hA) (hρ:=hρ) (hρhalf:=hρhalf) (hholder:=hholder)
    (hnull:=hnull) (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1) (J0:=J0) (hJH:=hJH) n

variable (haP:SmoothCylinders.BoundedSmooth P.coefficient)
variable (hAs:SmoothCylinders.BoundedSmooth (fun z=>κ+aV z))(hJ:StandardFiniteIto.Universal 𝓕 μ H J)
variable (hsmallPoint:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (hJF:(RemainderBandSpans.span P.exponent (J0+1):ℝ)≤NativeUniversalConstants.rowHorizon 1)
variable (hJC:(RemainderBandSpans.span P.exponent (J0+1):ℝ)≤4*Real.pi^2*NativeUniversalConstants.currentHorizon.{0} 1 (by omega))
variable (hJS:(RemainderBandSpans.span P.exponent (J0+1):ℝ)≤UniformFutureProfileScores.horizon 1)
variable (hlocalJ:StandardTerminalPastLocality J)(hF:StandardItoStoppedParameterFubini J)
variable (B4 B8:ℝ≥0)(hBDG4:StandardTerminalBDGPower 4 J B4)(hBDG8:StandardTerminalBDGPower 8 J B8)
local notation "SpanN" n:max=>RemainderBandSpans.span P.exponent (J0+n+1)
local notation "Cap" n:max=>(2*Cgamma)*(CompactMollifier.radius (J0+n+1)^(2*P.exponent)*(Neg).toReal+
  CompactMollifier.radius (J0+n+1)^(2*P.exponent+4*ρ)*
    ((Span n)^((P.exponent-1)/2)*Global+min 1 (Global/CompactMollifier.radius (J0+n+1)^2)))
local notation "Original"=>FullJointGammaMasterAbsolute.original
  (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
  (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (hκP:=hκP) (hH:=hH) (hnull:=hnull)
  (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1) (ha:=ha) (hA:=hA) (hρ:=hρ) (hρhalf:=hρhalf)
  (hholder:=hholder) (hL:=hL) (J0:=J0) (hJH:=hJH)
local notation "RowBound"=>sqrt (2*Cgamma)*(
  StateBands.geometricConstant P.exponent*Λ^(-P.exponent/4)*sqrt (Neg).toReal+
  StateBands.rootConstant (GammaDyadicWindowScale.alpha P.exponent ρ)*
    (sqrt Global)^(GammaDyadicWindowScale.alpha P.exponent ρ)+
  StateBands.geometricConstant (GammaDyadicWindowScale.degree P.exponent ρ)*
    Λ^(-GammaDyadicWindowScale.degree P.exponent ρ/4)*sqrt Global)

variable {Broot:ℝ}(hBroot:∀x,|a x|≤Broot)(hβsmall:P.exponent≤4/25)(hρeq:ρ=SHE.rho P.exponent)
variable (hJG:(RemainderBandSpans.span P.exponent (J0+1):ℝ)≤NativeTwoPointCovariance.horizon)
local notation "FrozenSource" n:max=>FrozenReferenceFullIdentity.original
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP (Span n) hH (a:=a) (J0+n) hL ρ hρ
local notation "FrozenBound"=>sqrt (NativeFrozenBesselScale.constant (2-P.exponent) κ ρ*
    (2*A*GaussianHeatBandRootEnvelope.constant P.exponent)^2)*
    StateBands.rootConstant (P.exponent+2*ρ)*
    (sqrt ((2*((1:ℝ)+(Bnext:ℝ)*PastReferenceBracket.energyConstant P κ 1 0 1))*Global))^(P.exponent+2*ρ)

include hIJ₀ hIJ₁ hBDG hsmall hBDGpast hJP hBDGγ hlocal hBDGnext hF haP hAs hJ
  hsmallPoint hJF hJC hJS hlocalJ hBDG4 hBDG8 hBroot hβsmall hρeq hJG in
/-- Both initial-completed first-pair fields are selected by their actual
original-noise constructions, with finite-prefix bounds fixed before
any upper frequency cutoff. -/
theorem exists_family(hActual:P.coefficient=(fun z=>κ+aV z))
    (hfreq:Λ^(1/4:ℝ)≤(2:ℝ)^(J0+1)):
    ∃(Fr Gm:ℕ→ℝ≥0×Ω→CircleL2),∃hmFr:∀n,Measurable (Fr n),∃hmGm:∀n,Measurable (Gm n),
      (∀n,∀ᵐt∂timeMeasure H,(fun ω=>Fr n (t,ω))=ᵐ[μ] (fun ω=>(FrozenSource n) (t,ω))) ∧
      (∀n,∀ᵐt∂timeMeasure H,(fun ω=>Gm n (t,ω))=ᵐ[μ] (fun ω=>Original n (t,ω))) ∧
      (∀n,Integrable (fun z=>‖Fr n z‖^2) (energyMeasure μ H)) ∧
      (∀n,Integrable (fun z=>‖Gm n z‖^2) (energyMeasure μ H)) ∧
      (∀L:ℕ,Integrable (fun z=>‖∑n∈Finset.range L,Fr n z‖^2) (energyMeasure μ H) ∧
        sqrt (∫z,‖∑n∈Finset.range L,Fr n z‖^2 ∂energyMeasure μ H)≤FrozenBound) ∧
      Summable (fun n=>sqrt (∫z,‖Gm n z‖^2 ∂energyMeasure μ H)) ∧
      (∑'n,sqrt (∫z,‖Gm n z‖^2 ∂energyMeasure μ H))≤RowBound:=by
  have hα1:GammaDyadicWindowScale.alpha P.exponent ρ<1:=by
    rw [hρeq]
    unfold GammaDyadicWindowScale.alpha SHE.rho
    linarith [P.exponent_pos]
  have hq:0<GammaDyadicWindowScale.degree P.exponent ρ:=by
    rw [hρeq]
    unfold GammaDyadicWindowScale.degree GammaDyadicWindowScale.alpha SHE.rho
    nlinarith [P.exponent_pos,sq_nonneg P.exponent]
  obtain ⟨Gm,W,hGm,hW,hGa,_,_,_,hiGm,hSummable,hTotal⟩:=FullJointGammaMasterAbsolute.master_output
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
    (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (J:=J) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (hH:=hH) (B:=B) (hBDG:=hBDG)
    (P:=P) (hκP:=hκP) (hsmall:=hsmall) (Bpast:=Bpast) (hBDGpast:=hBDGpast) (hL:=hL) (ha:=ha)
    (hA:=hA) (hρ:=hρ) (hρhalf:=hρhalf) (hholder:=hholder) (hnull:=hnull) (B0:=B0) (B1:=B1)
    (hBDG0:=hBDG0) (hBDG1:=hBDG1) (Bγ:=Bγ) (hBDGγ:=hBDGγ) (hlocal:=hlocal)
    (Bnext:=Bnext) (hBDGnext:=hBDGnext) (J0:=J0) (hJH:=hJH) (hJP:=hJP) (haP:=haP) (hAs:=hAs) (hJ:=hJ)
    (hsmallPoint:=hsmallPoint) (hJF:=hJF) (hJC:=hJC) (hJS:=hJS) (hlocalJ:=hlocalJ) (hF:=hF)
    (B4:=B4) (B8:=B8) (hBDG4:=hBDG4) (hBDG8:=hBDG8) hActual hα1 hq hfreq
  have hParam:=StandardItoStoppedParameterFubini.ambient J hF hnull
  obtain ⟨Fr,hFr,hiFr,hFa,hPrefix⟩:=FrozenReferenceFinitePrefixes.actual_prefixes
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
    (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (hκP:=hκP) (hH:=hH) (J:=J) (hF:=hParam)
    (hIJ0:=hIJ₀) (hIJ1:=hIJ₁) (hnull:=hnull) (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1)
    (ha:=ha) (hM0:=hBroot) (hΛ1:=hL) (ρ:=ρ) (hρ:=hρ) (hsmall:=hsmall) (hsmallrow:=hsmallPoint)
    (Bγ:=Bγ) (Bpast:=Bpast) (Bcur:=B) (hBDGγ:=hBDGγ) (hBDGpast:=hBDGpast) (hBDGcur:=hBDG)
    (hlocal:=hlocal) (Bnext:=Bnext) (hBDGnext:=hBDGnext) (hJ:=hJ) (hlocalJ:=hlocalJ)
    (hK:=hA) (hholder:=hholder) (hβsmall:=hβsmall) (hρhalf:=hρhalf) (hρeq:=hρeq)
    (J0:=J0) (hJH:=hJH) (hJP:=hJP) (hJG:=hJG)
  refine ⟨Fr,Gm,hFr,hGm,?_,hGa,hiFr,hiGm,hPrefix,hSummable,hTotal⟩
  intro n
  have hpos:0<Span n:=by exact_mod_cast spanPos n
  have hsP:Span n≤P.horizon:=spanP n
  have hWidth:0≤Width n:=sub_nonneg.mpr (spanH n)
  have hCover:Width n+Span n≤H:=by linarith
  have hid:=FrozenReferenceFullIdentity.identity_ae
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
    (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (hκP:=hκP) (W:=Width n) (h:=Span n)
    (hW:=hWidth) (hh:=hpos) (hcover:=hCover) (hH:=hH) (J:=J) (hIJ0:=hIJ₀) (hIJ1:=hIJ₁)
    (hnull:=hnull) (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1) (ha:=ha)
    (j:=J0+n) (hΛ1:=hL) (ρ:=ρ) (hρ:=hρ) (hsmall:=hsmall) (hwindow:=hsP)
    (Bγ:=Bγ) (Bpast:=Bpast) (hBDGγ:=hBDGγ) (hBDGpast:=hBDGpast) (hlocal:=hlocal)
    (Bnext:=Bnext) (hBDGnext:=hBDGnext) (by ring)
  filter_upwards [hFa n,hid] with t ht hi
  exact ht.trans (by simpa only [Real.toNNReal_coe] using hi)
end SHE.ActualFrozenGammaFamily
