module

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
namespace SHE.MovingOriginalGammaBands
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

/-- The actual original physical Gamma output at its own dyadic
window; no common moving version is assumed in this definition. -/
def output (n:ℕ)(r:ℝ):Ω→CircleL2:=MovingOriginalGammaHilbert.output
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hκP (Width n) (Span n)
  (sub_nonneg.mpr (spanH n)) (spanPos n) (by linarith) hH
  hnull B0 B1 hBDG0 hBDG1 ha hA hholder (J0+n) hL hρ hρhalf r
local notation "Output"=>output
  (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV)
  (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S)
  (P:=P) (hκP:=hκP) (hH:=hH) (hL:=hL) (ha:=ha) (hA:=hA) (hρ:=hρ) (hρhalf:=hρhalf)
  (hholder:=hholder) (hnull:=hnull) (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1)
  (J0:=J0) (hJH:=hJH)
def commonMeasure:Measure (ℝ×Ω):=(volume.restrict (Ioc (0:ℝ) H)).prod μ
local notation "Common"=>commonMeasure μ H

theorem zero_extension_energy (w:ℝ)(hw:w≤H)(G:ℝ×Ω→CircleL2)(hG:Measurable G):
    (∫⁻z,ENNReal.ofReal (‖if z.1∈Ioc (0:ℝ) w then G z else 0‖^2) ∂Common)=
      (∫⁻z,ENNReal.ofReal (‖G z‖^2) ∂(volume.restrict (Ioc (0:ℝ) w)).prod μ):=by
  classical
  have hF:Measurable (fun z:ℝ×Ω=>if z.1∈Ioc (0:ℝ) w then G z else 0):=
    hG.ite (measurableSet_Ioc.preimage measurable_fst) measurable_const
  rw [commonMeasure,lintegral_prod _ ((hF.norm.pow_const 2).ennreal_ofReal).aemeasurable,
    lintegral_prod _ ((hG.norm.pow_const 2).ennreal_ofReal).aemeasurable]
  have he:(fun r:ℝ=>∫⁻ω,ENNReal.ofReal (‖if r∈Ioc (0:ℝ) w then G (r,ω) else 0‖^2) ∂μ)=
      (Ioc (0:ℝ) w).indicator (fun r=>∫⁻ω,ENNReal.ofReal (‖G (r,ω)‖^2) ∂μ):=by
    funext r
    by_cases hr:r∈Ioc (0:ℝ) w <;> simp [hr]
  rw [he,lintegral_indicator measurableSet_Ioc]
  have hs:Ioc (0:ℝ) w⊆Ioc (0:ℝ) H:=fun r hr=>⟨hr.1,hr.2.trans hw⟩
  rw [Measure.restrict_restrict_of_subset hs]

variable (hF:StandardItoStoppedParameterFubini J)
include hIJ₀ hIJ₁ hΛ hBDG hsmall hBDGpast hJP hBDGγ hlocal hBDGnext hF in
/-- The ACTUAL Gamma bands are jointly Borel fields on ONE original
past/sample measure, extended by zero outside each own window. Their
energies are exactly the already proved original physical band energies. -/
theorem exists_bands:
    ∃G:ℕ→ℝ×Ω→CircleL2,
      (∀n,Measurable (G n)) ∧
      (∀n r ω,r∉Ioc (0:ℝ) (Width n)→G n (r,ω)=0) ∧
      (∀n,∀ᵐr∂volume.restrict (Ioc (0:ℝ) (Width n)),
        (fun ω=>G n (r,ω))=ᵐ[μ] Output n r) ∧
      (∀n,(∫⁻z,ENNReal.ofReal (‖G n z‖^2) ∂Common)=Band n) ∧
      ∀n,(∫⁻z,ENNReal.ofReal (‖G n z‖^2) ∂Common)<∞:=by
  classical
  have hb(n:ℕ):∃G:ℝ×Ω→CircleL2,Measurable G ∧
      (∀ᵐr∂volume.restrict (Ioc (0:ℝ) (Width n)),(fun ω=>G (r,ω))=ᵐ[μ] Output n r) ∧
      (∫⁻z,ENNReal.ofReal (‖G z‖^2) ∂(volume.restrict (Ioc (0:ℝ) (Width n))).prod μ)<∞:=by
    obtain ⟨Y,G,hY,hG,hYa,hGa,hE⟩:=MovingOriginalGammaSharp.exists_sharp_output
      (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV)
      (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S)
      (J:=J) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (hΛ:=hΛ) (hH:=hH) (B:=B) (hBDG:=hBDG)
      (P:=P) (hκP:=hκP) (h:=Span n) (W:=Width n) (hh:=spanPos n) (hhP:=spanP n)
      (hW0:=sub_nonneg.mpr (spanH n)) (hcover:=by linarith)
      (hsmall:=hsmall) (Bpast:=Bpast) (hBDGpast:=hBDGpast) (hL:=hL) (ha:=ha) (hA:=hA)
      (hρ:=hρ) (hρhalf:=hρhalf) (hholder:=hholder) (j:=J0+n) (hnull:=hnull)
      (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1) (Bγ:=Bγ) (hBDGγ:=hBDGγ)
      (hlocal:=hlocal) (Bnext:=Bnext) (hBDGnext:=hBDGnext) (hF:=hF)
    exact ⟨G,hG,hGa,lt_of_le_of_lt hE ENNReal.ofReal_lt_top⟩
  choose G hG hGa hGf using hb
  let F:ℕ→ℝ×Ω→CircleL2:=fun n z=>if z.1∈Ioc (0:ℝ) (Width n) then G n z else 0
  have hFm:∀n,Measurable (F n):=fun n=>(hG n).ite (measurableSet_Ioc.preimage measurable_fst) measurable_const
  have he(n:ℕ):(∫⁻z,ENNReal.ofReal (‖F n z‖^2) ∂Common)=
      (∫⁻z,ENNReal.ofReal (‖G n z‖^2) ∂(volume.restrict (Ioc (0:ℝ) (Width n))).prod μ):=
    zero_extension_energy μ H (Width n) (sub_le_self _ (spanPos n).le) (G n) (hG n)
  refine ⟨F,hFm,fun n r ω hr=>if_neg hr,?_,?_,fun n=>(he n).trans_lt (hGf n)⟩
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioc,hGa n] with r hr hrep
    simpa only [F,if_pos hr] using hrep
  · intro n
    rw [he n,lintegral_prod _ (((hG n).norm.pow_const 2).ennreal_ofReal).aemeasurable]
    apply lintegral_congr_ae
    filter_upwards [hGa n] with r hr
    apply lintegral_congr_ae
    filter_upwards [hr] with ω hω
    rw [hω]
    rfl
end SHE.MovingOriginalGammaBands

