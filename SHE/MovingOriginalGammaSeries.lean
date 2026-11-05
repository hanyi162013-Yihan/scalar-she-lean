module

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
namespace SHE.MovingOriginalGammaSeries
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

private theorem shift_preserving (s:ℝ):MeasurePreserving (fun t:ℝ=>t-s)
    (volume.restrict (Ioc s (H:ℝ))) (volume.restrict (Ioc (0:ℝ) ((H:ℝ)-s))):=by
  have hp:=((measurePreserving_sub_right (volume:Measure ℝ) s).restrict_preimage
    (measurableSet_Ioc:MeasurableSet (Ioc (0:ℝ) ((H:ℝ)-s))))
  convert hp using 1
  congr 1
  ext t
  simp only [mem_preimage,mem_Ioc]
  constructor <;> intro ht <;> constructor <;> linarith [ht.1,ht.2]

private theorem shift_energy (s:ℝ)(hs:0≤s)(G:ℝ×Ω→CircleL2)(hG:Measurable G):
    (∫⁻z,ENNReal.ofReal (‖if z.1∈Ioc s (H:ℝ) then G (z.1-s,z.2) else 0‖^2) ∂Common)=
      (∫⁻z,ENNReal.ofReal (‖G z‖^2) ∂(volume.restrict (Ioc (0:ℝ) ((H:ℝ)-s))).prod μ):=by
  classical
  have hShift:Measurable (fun z:ℝ×Ω=>G (z.1-s,z.2)):=
    hG.comp ((measurable_fst.sub_const s).prodMk measurable_snd)
  have hMask:Measurable (fun z:ℝ×Ω=>if z.1∈Ioc s (H:ℝ) then G (z.1-s,z.2) else 0):=
    hShift.ite (measurableSet_Ioc.preimage measurable_fst) measurable_const
  rw [commonMeasure,lintegral_prod _ ((hMask.norm.pow_const 2).ennreal_ofReal).aemeasurable,
    lintegral_prod _ ((hG.norm.pow_const 2).ennreal_ofReal).aemeasurable]
  have he:(fun t:ℝ=>∫⁻ω,ENNReal.ofReal (‖if t∈Ioc s (H:ℝ) then G (t-s,ω) else 0‖^2) ∂μ)=
      (Ioc s (H:ℝ)).indicator (fun t=>∫⁻ω,ENNReal.ofReal (‖G (t-s,ω)‖^2) ∂μ):=by
    funext t
    by_cases ht:t∈Ioc s (H:ℝ) <;> simp [ht]
  rw [he,lintegral_indicator measurableSet_Ioc,
    Measure.restrict_restrict_of_subset (show Ioc s (H:ℝ)⊆Ioc (0:ℝ) H from
      fun t ht=>⟨hs.trans_lt ht.1,ht.2⟩)]
  exact (shift_preserving H s).lintegral_comp
    (((hG.norm.pow_const 2).ennreal_ofReal).lintegral_prod_right')

local notation "RowBound"=>sqrt Cgamma*(
  StateBands.geometricConstant P.exponent*((2:ℝ)^(J0+1))^(-P.exponent)*sqrt (Neg).toReal+
  StateBands.rootConstant (GammaDyadicWindowScale.alpha P.exponent ρ)*
    (sqrt Global)^(GammaDyadicWindowScale.alpha P.exponent ρ)+
  StateBands.geometricConstant (GammaDyadicWindowScale.degree P.exponent ρ)*
    ((2:ℝ)^(J0+1))^(-GammaDyadicWindowScale.degree P.exponent ρ)*sqrt Global)
variable (hF:StandardItoStoppedParameterFubini J)

include hIJ₀ hIJ₁ hΛ hBDG hsmall hBDGpast hJP hBDGγ hlocal hBDGnext hF in
/-- The ACTUAL original-driver high Gamma bands converge in native
Hilbert L² and almost everywhere on ONE common original past/sample
measure. The sum has precisely the three sharp Gamma master-row gains;
all dependence among the bands is retained. -/
theorem summation (hα1:GammaDyadicWindowScale.alpha P.exponent ρ<1)
    (hq:0<GammaDyadicWindowScale.degree P.exponent ρ):
    ∃(F:ℕ→ℝ×Ω→CircleL2)(hFm:∀n,Measurable (F n))
      (hi:∀n,Integrable (fun z=>‖F n z‖^2) Common)
      (V:Lp CircleL2 2 Common)(W:ℝ×Ω→CircleL2),
      Measurable W ∧
      (∀n t ω,t∉Ioc (Span n) (H:ℝ)→F n (t,ω)=0) ∧
      (∀n,∀ᵐt∂volume.restrict (Ioc (Span n) (H:ℝ)),
        (fun ω=>F n (t,ω))=ᵐ[μ] Output n (t-Span n)) ∧
      HasSum (HilbertBandTails.vector Common F hFm hi) V ∧
      (∀ᵐz∂Common,HasSum (fun n=>F n z) (W z)) ∧
      (V=ᵐ[Common] W) ∧ Integrable (fun z=>‖W z‖^2) Common ∧
      Real.sqrt (∫z,‖W z‖^2 ∂Common)≤RowBound:=by
  classical
  obtain ⟨Gp,hGpm,hGpzero,hGprep,hEp,hfinp⟩:=MovingOriginalGammaBands.exists_bands
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV)
    (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S)
    (J:=J) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (hΛ:=hΛ) (hH:=hH) (B:=B) (hBDG:=hBDG)
    (P:=P) (hκP:=hκP) (hsmall:=hsmall) (Bpast:=Bpast) (hBDGpast:=hBDGpast)
    (hL:=hL) (ha:=ha) (hA:=hA) (hρ:=hρ) (hρhalf:=hρhalf) (hholder:=hholder)
    (hnull:=hnull) (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1)
    (Bγ:=Bγ) (hBDGγ:=hBDGγ) (hlocal:=hlocal) (Bnext:=Bnext) (hBDGnext:=hBDGnext)
    (J0:=J0) (hJH:=hJH) (hJP:=hJP) (hF:=hF)
  let F:ℕ→ℝ×Ω→CircleL2:=fun n z=>
    if z.1∈Ioc (Span n) (H:ℝ) then Gp n (z.1-Span n,z.2) else 0
  have hFm:∀n,Measurable (F n):=fun n=>
    ((hGpm n).comp ((measurable_fst.sub_const (Span n)).prodMk measurable_snd)).ite
      (measurableSet_Ioc.preimage measurable_fst) measurable_const
  have hFzero:∀n t ω,t∉Ioc (Span n) (H:ℝ)→F n (t,ω)=0:=fun n t ω ht=>if_neg ht
  have hFrep:∀n,∀ᵐt∂volume.restrict (Ioc (Span n) (H:ℝ)),
      (fun ω=>F n (t,ω))=ᵐ[μ] Output n (t-Span n):=by
    intro n
    have hp:∀ᵐt∂volume.restrict (Ioc (Span n) (H:ℝ)),
        (fun ω=>Gp n (t-Span n,ω))=ᵐ[μ] Output n (t-Span n):=
      (shift_preserving H (Span n)).quasiMeasurePreserving.ae (hGprep n)
    filter_upwards [hp,ae_restrict_mem measurableSet_Ioc] with t ht hmem
    simpa only [F,if_pos hmem] using ht
  have hown(n:ℕ):
      (∫⁻z,ENNReal.ofReal (‖Gp n z‖^2) ∂(volume.restrict (Ioc (0:ℝ) (Width n))).prod μ)=
        (∫⁻z,ENNReal.ofReal (‖Gp n z‖^2) ∂Common):=by
    rw [←MovingOriginalGammaBands.zero_extension_energy μ H (Width n)
      (sub_le_self _ (spanPos n).le) (Gp n) (hGpm n)]
    apply lintegral_congr
    intro z
    by_cases hz:z.1∈Ioc (0:ℝ) (Width n)
    · simp only [if_pos hz]
    · simp only [if_neg hz,hGpzero n z.1 z.2 hz,norm_zero,zero_pow (by norm_num:2≠0),ENNReal.ofReal_zero]
  have hE(n:ℕ):(∫⁻z,ENNReal.ofReal (‖F n z‖^2) ∂Common)=Band n:=
    (shift_energy μ H (Span n) (spanPos n).le (Gp n) (hGpm n)).trans ((hown n).trans (hEp n))
  have hfin(n:ℕ):(∫⁻z,ENNReal.ofReal (‖F n z‖^2) ∂Common)<∞:=
    (shift_energy μ H (Span n) (spanPos n).le (Gp n) (hGpm n)).trans_lt ((hown n).trans_lt (hfinp n))
  have hi(n:ℕ):Integrable (fun z=>‖F n z‖^2) Common:=by
    refine ⟨((hFm n).norm.pow_const 2).aestronglyMeasurable,?_⟩
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun z=>sq_nonneg ‖F n z‖))).mpr (hfin n)
  let Vn:=HilbertBandTails.vector Common F hFm hi
  have hnorm(n:ℕ):‖Vn n‖=sqrt (Band n).toReal:=by
    have he:‖Vn n‖^2=(Band n).toReal:=by
      rw [HilbertBandTails.vector_norm_sq]
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun z=>sq_nonneg ‖F n z‖))
        ((hFm n).norm.pow_const 2).aestronglyMeasurable]
      exact congrArg ENNReal.toReal (hE n)
    rw [←he,Real.sqrt_sq (norm_nonneg _)]
  have hs:=MixedNativeJointGammaBandSeries.series
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV)
    (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S)
    (J:=J) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (hΛ:=hΛ) (hH:=hH) (B:=B) (hBDG:=hBDG)
    (P:=P) (hκP:=hκP) (hsmall:=hsmall) (Bpast:=Bpast) (hBDGpast:=hBDGpast)
    (hL:=hL) (ha:=ha) (hA:=hA) (hρ:=hρ) (hρhalf:=hρhalf) (hholder:=hholder)
    (hnull:=hnull) (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1)
    (Bγ:=Bγ) (hBDGγ:=hBDGγ) (hlocal:=hlocal) (Bnext:=Bnext) (hBDGnext:=hBDGnext)
    (J0:=J0) (hJH:=hJH) (hJP:=hJP) hα1 hq
  have hnormsum:Summable (fun n=>‖Vn n‖):=by simpa only [hnorm] using hs.1
  have hsum:Summable Vn:=hnormsum.of_norm
  let V:Lp CircleL2 2 Common:=∑'n,Vn n
  let W:ℝ×Ω→CircleL2:=(Lp.aestronglyMeasurable V).mk V
  have hW:Measurable W:=(Lp.aestronglyMeasurable V).stronglyMeasurable_mk.measurable
  have hWa:V=ᵐ[Common] W:=(Lp.aestronglyMeasurable V).ae_eq_mk
  have hae:=Lp.hasSum_coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hnormsum)
  have hrep:∀ᵐz∂Common,∀n,Vn n z=F n z:=by
    rw [ae_all_iff]
    intro n
    exact ((memLp_two_iff_integrable_sq_norm (hFm n).aestronglyMeasurable).mpr (hi n)).coeFn_toLp
  have hWi:Integrable (fun z=>‖W z‖^2) Common:=
    (memLp_two_iff_integrable_sq_norm hW.aestronglyMeasurable).mp (MemLp.ae_eq hWa (Lp.memLp V))
  refine ⟨F,hFm,hi,V,W,hW,hFzero,hFrep,hsum.hasSum,?_,hWa,hWi,?_⟩
  · filter_upwards [hae,hrep,hWa] with z hz hr hWz
    change HasSum (fun n=>Vn n z) (V z) at hz
    simpa only [hr,hWz] using hz
  · have he:∫z,‖W z‖^2 ∂Common=‖V‖^2:=by
      rw [realLp_norm_sq]
      exact integral_congr_ae (hWa.symm.mono (fun z hz=>congrArg (fun x:CircleL2=>‖x‖^2) hz))
    rw [he,Real.sqrt_sq (norm_nonneg _)]
    exact (tsum_of_norm_bounded hs.1.hasSum (fun n=>(hnorm n).le)).trans hs.2
end SHE.MovingOriginalGammaSeries

