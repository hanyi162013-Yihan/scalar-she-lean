module

public import SHE.FullJointGammaOutput
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
namespace SHE.FullJointGammaMaster
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
/-- Literal full-time original Gamma band, including the initial triangle. -/
def original(n:ℕ):ℝ≥0×Ω→CircleL2:=FullJointGammaOutput.original
  (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
  (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (hκP:=hκP) (hH:=hH) (hnull:=hnull)
  (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1) (ha:=ha) (hA:=hA) (hρ:=hρ) (hρhalf:=hρhalf)
  (hholder:=hholder) (j:=J0+n) (hL:=hL) (h:=SpanN n) (hhH:=by exact_mod_cast spanH n) (spanPos n)
local notation "Original"=>original
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

include hIJ₀ hIJ₁ hBDG hsmall hBDGpast hJP hBDGγ hlocal hBDGnext hF haP hAs hJ
  hsmallPoint hJF hJC hJS hlocalJ hBDG4 hBDG8 in
/-- Full physical Gamma bands on the original time/sample measure.
The initial branch is identified before summation; all three sharp
master rows retain the original damping-frequency powers. -/
theorem master_output(hActual:P.coefficient=(fun z=>κ+aV z))
    (hα1:GammaDyadicWindowScale.alpha P.exponent ρ<1)
    (hq:0<GammaDyadicWindowScale.degree P.exponent ρ)
    (hfreq:Λ^(1/4:ℝ)≤(2:ℝ)^(J0+1)):
    ∃(F:ℕ→ℝ≥0×Ω→CircleL2)(W:ℝ≥0×Ω→CircleL2),
      (∀n,Measurable (F n)) ∧ Measurable W ∧
      (∀n,∀ᵐt∂timeMeasure H,(fun ω=>F n (t,ω))=ᵐ[μ] (fun ω=>Original n (t,ω))) ∧
      (∀ᵐz∂energyMeasure μ H,HasSum (fun n=>F n z) (W z)) ∧
      Integrable (fun z=>‖W z‖^2) (energyMeasure μ H) ∧
      Real.sqrt (∫z,‖W z‖^2 ∂energyMeasure μ H)≤RowBound:=by
  classical
  have hspan_le(c:ℝ)(hc:(RemainderBandSpans.span P.exponent (J0+1):ℝ)≤c)(n:ℕ):Span n≤c:=by
    exact le_trans (show Span n≤(RemainderBandSpans.span P.exponent (J0+1):ℝ) by
      exact_mod_cast RemainderBandSpans.span_antitone P.exponent_pos.le (show J0+1≤J0+n+1 by omega)) hc
  have hC:0≤2*Cgamma:=mul_nonneg (by norm_num)
    (MixedNativeJointGammaSharpEnergy.constant_pos
      (P:=P) (κ:=κ) (hκ:=hκ) (ell:=ell) (M:=M) (hell:=hell) (hκP:=hκP)
      (A:=A) (hρ:=hρ) (hρhalf:=hρhalf) (Bnext:=Bnext)).le
  have hb(n:ℕ):∃G:ℝ≥0×Ω→CircleL2,Measurable G ∧
      (∀ᵐt∂timeMeasure H,(fun ω=>G (t,ω))=ᵐ[μ] (fun ω=>Original n (t,ω))) ∧
      (∫⁻z,ENNReal.ofReal (‖G z‖^2) ∂energyMeasure μ H)≤ENNReal.ofReal (Cap n):=by
    obtain ⟨G,hG,hGa,hGe⟩:=FullJointGammaOutput.exists_output
      (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
      (I₀:=I₀) (I₁:=I₁) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (u₀:=u₀) (S:=S) (J:=J) (P:=P) (hκP:=hκP) (hH:=hH)
      (hsmallL2:=hsmall) (Bpast:=Bpast) (hBDGpast:=hBDGpast) (hnull:=hnull) (B0:=B0) (B1:=B1)
      (hBDG0:=hBDG0) (hBDG1:=hBDG1) (B:=Bγ) (hBDG:=hBDGγ) (hlocal:=hlocal) (Bnext:=Bnext) (hBDGnext:=hBDGnext)
      (a:=a) (ha:=ha) (A:=A) (ρ:=ρ) (hA:=hA) (hρ:=hρ) (hρhalf:=hρhalf) (hholder:=hholder) (j:=J0+n) (hL:=hL)
      (h:=SpanN n) (hhH:=by exact_mod_cast spanH n) (haP:=haP) (hJ:=hJ) (hAs:=hAs)
      (spanPos n) (spanP n) hsmallPoint hActual (hspan_le _ hJF n) (hspan_le _ hJC n) (hspan_le _ hJS n)
      hlocalJ hF B B4 B8 hBDG hBDG4 hBDG8
    refine ⟨G,hG,hGa,hGe.trans_eq ?_⟩
    rw [←ENNReal.ofReal_ofNat 2,←ENNReal.ofReal_mul (by norm_num:(0:ℝ)≤2)]
    congr 1
    ring
  choose F hFm hFa hFe using hb
  have hi(n:ℕ):Integrable (fun z=>‖F n z‖^2) (energyMeasure μ H):=by
    refine ⟨((hFm n).norm.pow_const 2).aestronglyMeasurable,?_⟩
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun z=>sq_nonneg ‖F n z‖))).mpr
      (lt_of_le_of_lt (hFe n) ENNReal.ofReal_lt_top)
  let Vn:=HilbertBandTails.vector (energyMeasure μ H) F hFm hi
  have hnorm(n:ℕ):‖Vn n‖≤sqrt (2*Cgamma)*(
      ((2:ℝ)^(J0+n+1))^(-P.exponent)*sqrt (Neg).toReal+
      ((2:ℝ)^(J0+n+1))^(-GammaDyadicWindowScale.alpha P.exponent ρ)*min 1 (sqrt Global*(2:ℝ)^(J0+n+1))+
      ((2:ℝ)^(J0+n+1))^(-GammaDyadicWindowScale.degree P.exponent ρ)*sqrt Global):=by
    have hGlobal:=MixedMovingEnergy.globalEnergy_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    have hS:0≤Span n:=by exact_mod_cast (spanPos n).le
    have hr:0≤CompactMollifier.radius (J0+n+1):=(CompactMollifier.radius_pos _).le
    have hraw:0≤Cap n:=by
      apply mul_nonneg hC
      apply add_nonneg (mul_nonneg (Real.rpow_nonneg hr _) ENNReal.toReal_nonneg)
      apply mul_nonneg (Real.rpow_nonneg hr _)
      exact add_nonneg (mul_nonneg (Real.rpow_nonneg hS _) hGlobal)
        (le_min zero_le_one (div_nonneg hGlobal (sq_nonneg _)))
    have he:‖Vn n‖^2≤Cap n:=by
      rw [HilbertBandTails.vector_norm_sq,integral_eq_lintegral_of_nonneg_ae
        (ae_of_all _ (fun z=>sq_nonneg ‖F n z‖)) ((hFm n).norm.pow_const 2).aestronglyMeasurable]
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hFe n)).trans_eq (ENNReal.toReal_ofReal hraw)
    have hs:‖Vn n‖^2≤(2*Cgamma)*(CompactMollifier.radius (J0+n+1)^(2*P.exponent)*(sqrt (Neg).toReal)^2+
        CompactMollifier.radius (J0+n+1)^(2*P.exponent+4*ρ)*
          ((Span n)^((P.exponent-1)/2)*(sqrt Global)^2+min 1 ((sqrt Global)^2/CompactMollifier.radius (J0+n+1)^2))):=by
      simpa only [Real.sq_sqrt ENNReal.toReal_nonneg,Real.sq_sqrt hGlobal] using he
    exact GammaDyadicWindowScale.norm_of_squared hC (sqrt_nonneg (Neg).toReal) (sqrt_nonneg Global) (J0+n+1) (Vn n) hs
  have hα0:0<GammaDyadicWindowScale.alpha P.exponent ρ:=by unfold GammaDyadicWindowScale.alpha;linarith [P.exponent_pos]
  have hs:=GammaDyadicNormEnvelope.sum_bound P.exponent_pos hα0 hα1 hq
    (sqrt_nonneg (2*Cgamma)) (sqrt_nonneg (Neg).toReal) (sqrt_nonneg Global) (J0+1) Vn
    (fun n=>by simpa only [show J0+1+n=J0+n+1 by omega] using hnorm n)
  have hn:=GammaDyadicNormEnvelope.sum_bound P.exponent_pos hα0 hα1 hq
    (sqrt_nonneg (2*Cgamma)) (sqrt_nonneg (Neg).toReal) (sqrt_nonneg Global) (J0+1) (fun n=>‖Vn n‖)
    (fun n=>by simpa only [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),show J0+1+n=J0+n+1 by omega] using hnorm n)
  have hnormsum:Summable (fun n=>‖Vn n‖):=hn.1
  let V:Lp CircleL2 2 (energyMeasure μ H):=∑'n,Vn n
  let W:ℝ≥0×Ω→CircleL2:=(Lp.aestronglyMeasurable V).mk V
  have hW:Measurable W:=(Lp.aestronglyMeasurable V).stronglyMeasurable_mk.measurable
  have hWa:V=ᵐ[energyMeasure μ H] W:=(Lp.aestronglyMeasurable V).ae_eq_mk
  have hae:=Lp.hasSum_coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hnormsum)
  have hrep:∀ᵐz∂energyMeasure μ H,∀n,Vn n z=F n z:=by
    rw [ae_all_iff]
    intro n
    exact ((memLp_two_iff_integrable_sq_norm (hFm n).aestronglyMeasurable).mpr (hi n)).coeFn_toLp
  have hWi:Integrable (fun z=>‖W z‖^2) (energyMeasure μ H):=
    (memLp_two_iff_integrable_sq_norm hW.aestronglyMeasurable).mp (MemLp.ae_eq hWa (Lp.memLp V))
  refine ⟨F,W,hFm,hW,hFa,?_,hWi,?_⟩
  · filter_upwards [hae,hrep,hWa] with z hz hr hw
    change HasSum (fun n=>Vn n z) (V z) at hz
    simpa only [hr,hw] using hz
  · have he:∫z,‖W z‖^2 ∂energyMeasure μ H=‖V‖^2:=by
      rw [realLp_norm_sq]
      exact integral_congr_ae (hWa.symm.mono (fun z hz=>congrArg (fun x:CircleL2=>‖x‖^2) hz))
    rw [he,Real.sqrt_sq (norm_nonneg _)]
    exact hs.2.trans (GammaFrequencyThreshold.three_rows (zero_lt_one.trans_le hL) hfreq
      P.exponent_pos hq (sqrt_nonneg (2*Cgamma)) (sqrt_nonneg (Neg).toReal) (sqrt_nonneg Global))
end SHE.FullJointGammaMaster
