module
import all SHE.CommonHigherGaussianFamily
import all SHE.CommonReferenceGaussianFamily
import all SHE.FullHigherClockIdentity
import all SHE.FullReferenceClockIdentity
import all SHE.CanonicalGaussianBareRoot
import all SHE.ActualGaussianComponentFamilies
import all SHE.FullFiniteGaussianResidual
public import SHE.ActualGaussianComponentFamilies
public import SHE.FullFiniteGaussianResidual
public import SHE.FullFirstDefectBandPrefixes
public import SHE.CommonHigherGaussianFamily
public import SHE.CommonReferenceGaussianFamily
public import SHE.MixedNativeHigherGaussianTailFamily
public import SHE.FiniteNativeGaussianCutoff
public import SHE.FullHigherClockIdentity
public import SHE.NativeGaussianWindowCutoff
public import SHE.NativeFullRateCap
public import SHE.HilbertENNRateTails
public import SHE.MixedNativeHigherFullOutput
public import SHE.CanonicalGaussianRootBands
public import SHE.MixedNativeHigherMovingRate
public import SHE.MixedNativeMovingEnvelopeRate
public import SHE.MixedNativeHigherSharpOutput
public import SHE.MixedNativeHigherSharpInitial
public import SHE.NativeOutputTimePatch
public import SHE.MixedNativeHigherMovingOutput
public import SHE.NativeOriginalOutputParameter
public import SHE.MovingNativePredictableAverages
public import SHE.MixedNativeHigherMovingEnergy
public import SHE.NativeCurrentWindowMeasure
public import SHE.MovingNativeAverageTranslation
public import SHE.MovingNativeColumnTranslation
public import SHE.MovingNativeColumnAverages
public import SHE.MixedPastNativeCompleteColumns
public import SHE.ShiftedOldTimeMeasure
public import SHE.MovingNativeColumns
public import SHE.MixedPastNativeOldTimeEnergy
public import SHE.MixedPastSignedEndpointFields
public import SHE.NativeKernelCongruence
public import SHE.ShiftedPhysicalArrays
public import SHE.NativeRowTimeShift
public import SHE.MovingNativeSpatialKernel
public import SHE.ControlledMeanSpatialShift
public import SHE.MixedPastNativeKernelSemigroup

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
namespace SHE.ActualGaussianMarkedFamily
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedNativeHigherSharpOutput_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeHigherSharpOutput_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeHigherSharpOutput_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeHigherSharpOutput_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeHigherSharpOutput_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeHigherSharpOutput_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
open PastItoInputs PastItoAlgebra PhysicalProfile


local instance mixedNativeHigherSharpOutput_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedNativeHigherSharpOutput_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance mixedNativeHigherSharpOutput_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedNativeHigherSharpOutput_nativeSecond:SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (D:SmoothApproximation.ScalarData){T:ℝ}(hT:0<T)(hT1:T≤1)
    (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2)
variable (n:ℕ)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)(hJ:StandardFiniteIto.Universal 𝓕 μ H J)
variable (hAs:BoundedSmooth (fun z=>κ+aV z))

local notation "Smooth"=>ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall
local notation "Pzero"=>Smooth 0
local notation "Rough"=>ControlledSmoothLimit.roughTotalParameters D hT hT1 hsmall
local notation "scoreFloor"=>ControlledOldIntervals.fraction Pzero*(Pzero).lower
local notation "Cs"=>PhysicalScoreChain.uniformConstant 1
local notation "Global"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Neg"=>MixedActualEnergyBridge.negativeEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
variable (N Jbase:ℕ)(ρ χ χref η ε tail ζ εref ηref:ℝ)
  (hρ:0<ρ)(hχ0:0≤χ)(hχ1:χ<1)(hm:χ<D.beta+2*ρ)
  (hα:0<ρ+η)(hαhalf:ρ+η<1/2)(hζ:0<ζ)
  (hχref:0<χref)(hχref1:χref<1)(hεref:0≤εref)(hεrefhalf:εref<1/2)(hηref:0<ηref)
  (p:ℕ)(hp:0<p)(Bcur Bword Bref:ℕ→ℝ≥0)
local notation "Bare"=>CanonicalGaussianBareRoot.test D n
local notation "BU"=>CanonicalGaussianBareRoot.uniform D n
local notation "BM"=>CanonicalGaussianBareRoot.measurable D n
local notation "OriginalR"=>FullReferenceClockIdentity.original
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P J hIJ₀ hIJ₁ hnull hJ hAs
local notation "OriginalH"=>FullHigherClockIdentity.original
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P J hIJ₀ hIJ₁ hnull hJ hAs

/-- Actual reference components at a single cutoff shared by all finite depths. -/
def reference(k j:ℕ)(hL:1≤Λ):ℝ≥0×Ω→CircleL2:=
  MixedNativeReferenceGaussianFamily.actual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP D n
    (fun _:HeatCircle=>(1:ℝ)) measurable_const (W:=1) zero_le_one (fun _=>by norm_num)
    hL hρ.le (k+1) (j+Jbase+1)
local notation "Ref"=>reference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP D n Jbase ρ hρ

variable (hκP:κ<P.lower)(hH:(H:ℝ)≤1)(hL:1≤Λ)(hρhalf:ρ<1/2)
  (BI0 BI1 B16:ℝ≥0)
  (hBI0:StandardTerminalBDG16 I₀ BI0)(hBI1:StandardTerminalBDG16 I₁ BI1)(hB16:StandardTerminalBDG16 J B16)
  (hJH:(RemainderBandSpans.span P.exponent (Jbase+1):ℝ)≤H)
local notation "haD"=>D.smooth_boundedSmooth n
local notation "Span" j:max=>RemainderBandSpans.span P.exponent (Jbase+j+1)
theorem holder_param(hParam:P=Smooth n):
    ∀x y,|D.smoothCoefficient n x-D.smoothCoefficient n y|≤D.holderConstant*|x-y|^P.exponent:=by
  have he:P.exponent=D.beta:=by rw [hParam];rfl
  simpa only [he] using D.smooth_holder n
theorem span_H(j:ℕ)(hCut:(RemainderBandSpans.span P.exponent (Jbase+1):ℝ)≤H):Span j≤H:=by
  apply NNReal.coe_le_coe.mp
  exact (show (Span j:ℝ)≤RemainderBandSpans.span P.exponent (Jbase+1) from by
    exact_mod_cast RemainderBandSpans.span_antitone P.exponent_pos.le (show Jbase+1≤Jbase+j+1 by omega)).trans hCut
local notation "SpanH" j:max=>span_H H P Jbase j hJH
local notation "FrSource" j:max=>FrozenReferenceFullIdentity.original
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP (Span j:ℝ) hH
    (a:=D.smoothCoefficient n) (Jbase+j) hL ρ hρ
def gammaSource(hParam:P=Smooth n)(j:ℕ):ℝ≥0×Ω→CircleL2:=FullJointGammaOutput.original
  (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
  (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (hκP:=hκP) (hH:=hH) (hnull:=hnull)
  (B0:=BI0) (B1:=BI1) (hBDG0:=hBI0) (hBDG1:=hBI1) (ha:=haD) (A:=D.holderConstant) (hA:=D.holderConstant_nonneg)
  (hρ:=hρ) (hρhalf:=hρhalf) (hholder:=holder_param P D hT hT1 hsmall n hParam) (j:=Jbase+j) (hL:=hL) (h:=Span j) (hhH:=span_H H P Jbase j hJH)
    (RemainderBandSpans.span_pos P.exponent (Jbase+j+1))
local notation "GmSource" hp:max j:max=>gammaSource
  (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
  (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (D:=D) (hT:=hT) (hT1:=hT1) (hsmall:=hsmall) (n:=n)
  (Jbase:=Jbase) (ρ:=ρ) (hρ:=hρ) (hκP:=hκP) (hH:=hH) (hL:=hL) (hρhalf:=hρhalf) (hParam:=hp)
  (hnull:=hnull) (BI0:=BI0) (BI1:=BI1) (hBI0:=hBI0) (hBI1:=hBI1) (hJH:=hJH) j
local notation "Mark" Fr:max Gm:max Rf:max Nf:max j:max=>FullFiniteGaussianResidual.residual
  (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
  (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (ha:=haD) (j:=Jbase+j) (hL:=hL) (hρ:=hρ) (h:=Span j) (haP:=haP)
    N (Fr j) (Gm j) (fun k=>Rf k j) (fun k=>Nf k j)

theorem reference_bare(j k:ℕ)(z:ℝ≥0×Ω):
    OriginalR (Bare (Jbase+j+1)) (BU (Jbase+j+1)) (BM (Jbase+j+1)) (Span j) hL hρ.le k z=
      FullFiniteGaussianResidual.reference
        (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
        (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (J:=J) (P:=P) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁)
        (hnull:=hnull) (hJ:=hJ) (hAs:=hAs) (a:=D.smoothCoefficient n) (ha:=haD) (j:=Jbase+j) (hL:=hL) (hρ:=hρ) (h:=Span j) k z:=by
  rfl

theorem higher_bare(j k:ℕ)(z:ℝ≥0×Ω):
    OriginalH (Bare (Jbase+j+1)) (BU (Jbase+j+1)) (BM (Jbase+j+1)) (Span j) hL hρ.le k z=
      FullFiniteGaussianResidual.higher
        (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
        (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (J:=J) (P:=P) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁)
        (hnull:=hnull) (hJ:=hJ) (hAs:=hAs) (a:=D.smoothCoefficient n) (ha:=haD) (j:=Jbase+j) (hL:=hL) (hρ:=hρ) (h:=Span j) k z:=by
  rfl

include hJH hL hρhalf hρ haP hAs hIJ₀ hIJ₁ hJ hκP hH hnull hχ0 hχ1 hm hα hαhalf hζ hχref hχref1 hεref hεrefhalf hηref hp hBI0 hBI1 hB16 in
/-- Actual finite-depth component selection at one common cutoff, followed by
the genuine Borel marked residual. Only the already constructed frozen/Gamma
versions are supplied; every reference/higher component is obtained here. -/
theorem exists_marked(hA:P.coefficient=(fun z=>κ+aV z))(hCanonical:P=Smooth n)
    (hlocal:StandardTerminalPastLocality J)(hHpos:0<H)
    (hsmallProfile:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (B1:ℝ≥0)(hBDG1:StandardTerminalBDGPower 1 J B1)
    (hBDGcur:∀k,k<N→StandardTerminalBDGPower (p*(k+3)) J (Bcur k))
    (hBDGword:∀k,k<N→StandardTerminalBDGPower (k+3) J (Bword k))
    (hBDGref:∀k,k<N→StandardTerminalBDGPower ((2*p)*(k+3)) J (Bref k))
    (horder:1≤(p:ℝ)*(1-χ))(horderref:1≤(p:ℝ)*(1-χref))
    (htail:tail≤ε*(2*((p-1:ℕ):ℝ)))(hη:0<η)(hFubini:StandardItoParameterFubini J)
    (hJbase:FiniteNativeGaussianCutoff.index D hT hT1 hsmall H hHpos N≤Jbase)
    (Fr Gm:ℕ→ℝ≥0×Ω→CircleL2)(hmFr:∀j,Measurable (Fr j))(hmGm:∀j,Measurable (Gm j))
    (hFr:∀j,∀ᵐt∂timeMeasure H,∀ᵐω∂μ,Fr j (t,ω)=(FrSource j) (t,ω))
    (hGm:∀j,∀ᵐt∂timeMeasure H,∀ᵐω∂μ,Gm j (t,ω)=(GmSource hCanonical j) (t,ω)):
    ∃Rf Nf:ℕ→ℕ→ℝ≥0×Ω→CircleL2,
      (∀k,k<N→∀j,Measurable (Rf k j)) ∧ (∀k,k<N→∀j,Measurable (Nf k j)) ∧
      (∀k,k<N→∀j,Integrable (fun z=>‖Rf k j z‖^2) (energyMeasure μ H)) ∧
      (∀k,k<N→∀j,Integrable (fun z=>‖Nf k j z‖^2) (energyMeasure μ H)) ∧
      (∀k,k<N→∀j,∀ᵐt∂timeMeasure H,∀ᵐω∂μ,Rf k j (t,ω)=
        OriginalR (Bare (j+Jbase+1)) (BU (j+Jbase+1)) (BM (j+Jbase+1))
          (RemainderBandSpans.span D.beta (j+Jbase+1)) hL hρ.le (k+1) (t,ω)) ∧
      (∀k,k<N→∀j,∀ᵐt∂timeMeasure H,∀ᵐω∂μ,Nf k j (t,ω)=
        OriginalH (Bare (j+Jbase+1)) (BU (j+Jbase+1)) (BM (j+Jbase+1))
          (RemainderBandSpans.span D.beta (j+Jbase+1)) hL hρ.le (k+1) (t,ω)) ∧
      (∀j,Measurable (Mark Fr Gm Rf Nf j)) ∧
      (∀j,∀ᵐt∂timeMeasure H,∀ᵐω∂μ,(Mark Fr Gm Rf Nf j) (t,ω)=
        ∑k∈Finset.range (N+1),FullFirstDefectBandEnergy.term
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hAs haD (Span j) (Jbase+j) hL hρ.le k (t,ω)):=by
  obtain ⟨Y,hRm,hYm,hRa,hYa,hRi,hYi⟩:=ActualGaussianComponentFamilies.exists_family
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP D hT hT1 hsmall n
    J hIJ₀ hIJ₁ hnull hJ hAs N Jbase ρ χ χref η ε tail ζ εref ηref
    hρ hχ0 hχ1 hm hα hαhalf hζ hχref hχref1 hεref hεrefhalf hηref p hp Bcur Bword Bref
    hA hlocal hL hρhalf hHpos hH hsmallProfile hsmallL2 B1 hBDG1 hCanonical
    hBDGcur hBDGword hBDGref horder horderref htail hη hFubini hJbase
  let Rf:ℕ→ℕ→ℝ≥0×Ω→CircleL2:=fun k j=>Ref k j hL
  let Nf:ℕ→ℕ→ℝ≥0×Ω→CircleL2:=fun k j=>if hk:k<N then Y ⟨k,hk⟩ j else 0
  have he:P.exponent=D.beta:=by rw [hCanonical];rfl
  have hRm'(k:ℕ)(hk:k<N)(j:ℕ):Measurable (Rf k j):=hRm ⟨k,hk⟩ j
  have hNm'(k:ℕ)(hk:k<N)(j:ℕ):Measurable (Nf k j):=by simpa only [Nf,dif_pos hk] using hYm ⟨k,hk⟩ j
  refine ⟨Rf,Nf,hRm',hNm',fun k hk j=>hRi ⟨k,hk⟩ j,?_,?_,?_,?_,?_⟩
  · intro k hk j
    simpa only [Nf,dif_pos hk] using hYi ⟨k,hk⟩ j
  · intro k hk j
    exact hRa ⟨k,hk⟩ j
  · intro k hk j
    simpa only [Nf,dif_pos hk] using hYa ⟨k,hk⟩ j
  · intro j
    exact FullFiniteGaussianResidual.measurable
      (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
      (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (ha:=haD) (j:=Jbase+j) (hL:=hL) (hρ:=hρ) (h:=Span j) (haP:=haP)
      N (Fr j) (Gm j) (fun k=>Rf k j) (fun k=>Nf k j) (hmFr j) (hmGm j)
      (fun k hk=>hRm' k hk j) (fun k hk=>hNm' k hk j)
  · intro j
    have hRall:∀ᵐt∂timeMeasure H,∀ᵐω∂μ,∀k,k<N→Rf k j (t,ω)=
        FullFiniteGaussianResidual.reference
          (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
          (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (J:=J) (P:=P) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁)
          (hnull:=hnull) (hJ:=hJ) (hAs:=hAs) (a:=D.smoothCoefficient n) (ha:=haD) (j:=Jbase+j) (hL:=hL) (hρ:=hρ) (h:=Span j) (k+1) (t,ω):=by
      have ht:∀ᵐt∂timeMeasure H,∀k:Fin N,∀ᵐω∂μ,Ref k j hL (t,ω)=
          OriginalR (Bare (j+Jbase+1)) (BU (j+Jbase+1)) (BM (j+Jbase+1))
            (RemainderBandSpans.span D.beta (j+Jbase+1)) hL hρ.le (k+1) (t,ω):=
        ae_all_iff.mpr (fun k=>hRa k j)
      filter_upwards [ht] with t ht
      filter_upwards [ae_all_iff.mpr ht] with ω hω
      intro k hk
      have hc:=hω ⟨k,hk⟩
      simp only [Rf,he,show Jbase+j=j+Jbase by omega,show Jbase+j+1=j+Jbase+1 by omega] at ⊢
      have hb:=reference_bare
        (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
        (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (J:=J) (P:=P) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁)
        (hnull:=hnull) (hJ:=hJ) (hAs:=hAs) (D:=D) (n:=n) (Jbase:=Jbase) (hL:=hL) (ρ:=ρ) (hρ:=hρ) (j:=j) (k:=k+1) (z:=(t,ω))
      simp only [he,show Jbase+j=j+Jbase by omega] at hb
      exact hc.trans hb
    have hNall:∀ᵐt∂timeMeasure H,∀ᵐω∂μ,∀k,k<N→Nf k j (t,ω)=
        FullFiniteGaussianResidual.higher
          (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
          (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (J:=J) (P:=P) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁)
          (hnull:=hnull) (hJ:=hJ) (hAs:=hAs) (a:=D.smoothCoefficient n) (ha:=haD) (j:=Jbase+j) (hL:=hL) (hρ:=hρ) (h:=Span j) (k+1) (t,ω):=by
      have ht:=ae_all_iff.mpr (fun k:Fin N=>hYa k j)
      filter_upwards [ht] with t ht
      filter_upwards [ae_all_iff.mpr ht] with ω hω
      intro k hk
      have hc:=hω ⟨k,hk⟩
      simp only [Nf,dif_pos hk,he,show Jbase+j=j+Jbase by omega,show Jbase+j+1=j+Jbase+1 by omega] at ⊢
      have hb:=higher_bare
        (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
        (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (J:=J) (P:=P) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁)
        (hnull:=hnull) (hJ:=hJ) (hAs:=hAs) (D:=D) (n:=n) (Jbase:=Jbase) (hL:=hL) (ρ:=ρ) (hρ:=hρ) (j:=j) (k:=k+1) (z:=(t,ω))
      simp only [he,show Jbase+j=j+Jbase by omega] at hb
      exact hc.trans hb
    exact FullFiniteGaussianResidual.identified
      (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
      (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (J:=J) (P:=P) (hκP:=hκP) (hH:=hH)
      (B:=B16) (hBDG:=hB16) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (ha:=haD) (j:=Jbase+j) (hnull:=hnull)
      (B0:=BI0) (B1:=BI1) (hBDG0:=hBI0) (hBDG1:=hBI1) (hA:=D.holderConstant_nonneg) (hholder:=holder_param P D hT hT1 hsmall n hCanonical)
      (hAs:=hAs) (hJ:=hJ) (hL:=hL) (hρ:=hρ) (hρhalf:=hρhalf) (h:=Span j) (hhH:=span_H H P Jbase j hJH) (haP:=haP)
      (RemainderBandSpans.span_pos P.exponent (Jbase+j+1)) hsmallProfile hA hlocal hFubini
      N (Fr j) (Gm j) (fun k=>Rf k j) (fun k=>Nf k j) (hFr j) (hGm j) hRall hNall
end SHE.ActualGaussianMarkedFamily
