module
import all SHE.ActualGaussianMarkedFamily
import all SHE.ActualFrozenGammaFamily
import all SHE.FullJointGammaMasterAbsolute
public import SHE.ActualGaussianMarkedFamily
public import SHE.ActualFrozenGammaFamily
public import SHE.FullFiniteGaussianRMS
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
namespace SHE.ActualGaussianFullFamily
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
variable (Bpast:ℝ≥0)(hBDGpast:StandardTerminalBDGPower 2 J Bpast)
  (hlocalI:StandardTerminalPastLocality I₁)(Bnext:ℝ≥0)(hBDGnext:StandardTerminalBDGPower 1 I₁ Bnext)
  (hFstop:StandardItoStoppedParameterFubini J)(B4 B8:ℝ≥0)
  (hBDG4:StandardTerminalBDGPower 4 J B4)(hBDG8:StandardTerminalBDGPower 8 J B8)
  (hβsmall:P.exponent≤4/25)(hρeq:ρ=SHE.rho P.exponent)
  (hJP:(RemainderBandSpans.span P.exponent (Jbase+1):ℝ)≤P.horizon)
  (hJF:(RemainderBandSpans.span P.exponent (Jbase+1):ℝ)≤NativeUniversalConstants.rowHorizon 1)
  (hJC:(RemainderBandSpans.span P.exponent (Jbase+1):ℝ)≤4*Real.pi^2*NativeUniversalConstants.currentHorizon.{0} 1 (by omega))
  (hJS:(RemainderBandSpans.span P.exponent (Jbase+1):ℝ)≤UniformFutureProfileScores.horizon 1)
  (hJG:(RemainderBandSpans.span P.exponent (Jbase+1):ℝ)≤NativeTwoPointCovariance.horizon)
local notation "Mark" Fr:max Gm:max Rf:max Nf:max j:max=>FullFiniteGaussianResidual.residual
  (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
  (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (ha:=haD) (j:=Jbase+j) (hL:=hL) (hρ:=hρ) (h:=Span j) (haP:=haP)
    N (Fr j) (Gm j) (fun k=>Rf k j) (fun k=>Nf k j)
local notation "Cgamma"=>JointGammaConstants.nativeConstant P D.holderConstant κ ell M hell hκP hρ hρhalf Bnext
local notation "FrBound"=>sqrt (NativeFrozenBesselScale.constant (2-P.exponent) κ ρ*
    (2*D.holderConstant*GaussianHeatBandRootEnvelope.constant P.exponent)^2)*
    StateBands.rootConstant (P.exponent+2*ρ)*
    (sqrt ((2*((1:ℝ)+(Bnext:ℝ)*PastReferenceBracket.energyConstant P κ 1 0 1))*Global))^(P.exponent+2*ρ)
local notation "GmBound"=>sqrt (2*Cgamma)*(
  StateBands.geometricConstant P.exponent*Λ^(-P.exponent/4)*sqrt (Neg ρ).toReal+
  StateBands.rootConstant (GammaDyadicWindowScale.alpha P.exponent ρ)*
    (sqrt Global)^(GammaDyadicWindowScale.alpha P.exponent ρ)+
  StateBands.geometricConstant (GammaDyadicWindowScale.degree P.exponent ρ)*
    Λ^(-GammaDyadicWindowScale.degree P.exponent ρ/4)*sqrt Global)

include hχ0 hχ1 hm hα hαhalf hζ hχref hχref1 hεref hεrefhalf hηref hp
  hIJ₀ hIJ₁ hJ hκP hH hnull hBI0 hBI1 hB16 hBDGpast hlocalI hBDGnext hFstop hBDG4 hBDG8
  hJH hJP hJF hJC hJS hJG hβsmall hρeq in
/-- All actual full-time fields needed by the fixed finite stochastic
comparison are chosen on one common cutoff. No component version or
analytic comparison bound is assumed. -/
theorem exists_family(hActual:P.coefficient=(fun z=>κ+aV z))(hCanonical:P=Smooth n)
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
    (htail:tail≤ε*(2*((p-1:ℕ):ℝ)))(hη:0<η)
    (hJbase:FiniteNativeGaussianCutoff.index D hT hT1 hsmall H hHpos N≤Jbase)
    (hfreq:Λ^(1/4:ℝ)≤(2:ℝ)^(Jbase+1)):
    ∃Fr Gm:ℕ→ℝ≥0×Ω→CircleL2,∃Rf Nf:ℕ→ℕ→ℝ≥0×Ω→CircleL2,
      (∀j,Measurable (Fr j)) ∧ (∀j,Measurable (Gm j)) ∧
      (∀k,k<N→∀j,Measurable (Rf k j)) ∧ (∀k,k<N→∀j,Measurable (Nf k j)) ∧
      (∀k,k<N→∀j,Integrable (fun z=>‖Rf k j z‖^2) (energyMeasure μ H)) ∧
      (∀k,k<N→∀j,Integrable (fun z=>‖Nf k j z‖^2) (energyMeasure μ H)) ∧
      (∀j,Measurable (Mark Fr Gm Rf Nf j)) ∧
      (∀j,∀ᵐt∂timeMeasure H,∀ᵐω∂μ,(Mark Fr Gm Rf Nf j) (t,ω)=
        ∑k∈Finset.range (N+1),FullFirstDefectBandEnergy.term
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hAs haD (Span j) (Jbase+j) hL hρ.le k (t,ω)) ∧
      (∀k,k<N→∀j,∀ᵐt∂timeMeasure H,∀ᵐω∂μ,Rf k j (t,ω)=
        OriginalR (Bare (j+Jbase+1)) (BU (j+Jbase+1)) (BM (j+Jbase+1))
          (RemainderBandSpans.span D.beta (j+Jbase+1)) hL hρ.le (k+1) (t,ω)) ∧
      (∀k,k<N→∀j,∀ᵐt∂timeMeasure H,∀ᵐω∂μ,Nf k j (t,ω)=
        OriginalH (Bare (j+Jbase+1)) (BU (j+Jbase+1)) (BM (j+Jbase+1))
          (RemainderBandSpans.span D.beta (j+Jbase+1)) hL hρ.le (k+1) (t,ω)) ∧
      (∀j,Integrable (fun z=>‖Gm j z‖^2) (energyMeasure μ H)) ∧
      (∀L:ℕ,Integrable (fun z=>‖∑j∈Finset.range L,Fr j z‖^2) (energyMeasure μ H) ∧
        sqrt (∫z,‖∑j∈Finset.range L,Fr j z‖^2 ∂energyMeasure μ H)≤FrBound) ∧
      Summable (fun j=>sqrt (∫z,‖Gm j z‖^2 ∂energyMeasure μ H)) ∧
      (∑'j,sqrt (∫z,‖Gm j z‖^2 ∂energyMeasure μ H))≤GmBound:=by
  have hHolder:=ActualGaussianMarkedFamily.holder_param P D hT hT1 hsmall n hCanonical
  obtain ⟨Fr,Gm,hmFr,hmGm,hFr,hGm,_,hiGm,hFrPrefix,hsGm,hTotal⟩:=ActualFrozenGammaFamily.exists_family
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
    (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (J:=J) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (hH:=hH) (B:=B1) (hBDG:=hBDG1)
    (P:=P) (hκP:=hκP) (hsmall:=hsmallL2) (Bpast:=Bpast) (hBDGpast:=hBDGpast) (hL:=hL) (ha:=haD)
    (hA:=D.holderConstant_nonneg) (hρ:=hρ) (hρhalf:=hρhalf) (hholder:=hHolder) (hnull:=hnull) (B0:=BI0) (B1:=BI1)
    (hBDG0:=hBI0) (hBDG1:=hBI1) (Bγ:=B16) (hBDGγ:=hB16) (hlocal:=hlocalI)
    (Bnext:=Bnext) (hBDGnext:=hBDGnext) (J0:=Jbase) (hJH:=hJH) (hJP:=hJP) (haP:=haP) (hAs:=hAs) (hJ:=hJ)
    (hsmallPoint:=hsmallProfile) (hJF:=hJF) (hJC:=hJC) (hJS:=hJS) (hlocalJ:=hlocal) (hF:=hFstop)
    (B4:=B4) (B8:=B8) (hBDG4:=hBDG4) (hBDG8:=hBDG8)
    (hBroot:=ScalarApproximationDiscrepancy.smooth_abs_bound D n) (hβsmall:=hβsmall) (hρeq:=hρeq) (hJG:=hJG)
    hActual hfreq
  have hGm'(j:ℕ):∀ᵐt∂timeMeasure H,∀ᵐω∂μ,Gm j (t,ω)=ActualGaussianMarkedFamily.gammaSource
      (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
      (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (D:=D) (hT:=hT) (hT1:=hT1) (hsmall:=hsmall) (n:=n)
      (Jbase:=Jbase) (ρ:=ρ) (hρ:=hρ) (hκP:=hκP) (hH:=hH) (hL:=hL) (hρhalf:=hρhalf)
      (hnull:=hnull) (BI0:=BI0) (BI1:=BI1) (hBI0:=hBI0) (hBI1:=hBI1) (hJH:=hJH) hCanonical j (t,ω):=by
    filter_upwards [hGm j] with t ht
    filter_upwards [ht] with ω hω
    simpa only [FullJointGammaMasterAbsolute.original,ActualGaussianMarkedFamily.gammaSource] using hω
  obtain ⟨Rf,Nf,hmRf,hmNf,hiRf,hiNf,hRa,hNa,hmMark,hMark⟩:=ActualGaussianMarkedFamily.exists_marked
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
    (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (haP:=haP) (D:=D) (hT:=hT) (hT1:=hT1) (hsmall:=hsmall) (n:=n)
    (J:=J) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (hnull:=hnull) (hJ:=hJ) (hAs:=hAs) (N:=N) (Jbase:=Jbase)
    (ρ:=ρ) (χ:=χ) (χref:=χref) (η:=η) (ε:=ε) (tail:=tail) (ζ:=ζ) (εref:=εref) (ηref:=ηref)
    (hρ:=hρ) (hχ0:=hχ0) (hχ1:=hχ1) (hm:=hm) (hα:=hα) (hαhalf:=hαhalf) (hζ:=hζ)
    (hχref:=hχref) (hχref1:=hχref1) (hεref:=hεref) (hεrefhalf:=hεrefhalf) (hηref:=hηref)
    (p:=p) (hp:=hp) (Bcur:=Bcur) (Bword:=Bword) (Bref:=Bref) (hκP:=hκP) (hH:=hH) (hL:=hL) (hρhalf:=hρhalf)
    (BI0:=BI0) (BI1:=BI1) (B16:=B16) (hBI0:=hBI0) (hBI1:=hBI1) (hB16:=hB16) (hJH:=hJH)
    hActual hCanonical hlocal hHpos hsmallProfile hsmallL2 B1 hBDG1 hBDGcur hBDGword hBDGref
    horder horderref htail hη (StandardItoStoppedParameterFubini.ambient J hFstop hnull) hJbase Fr Gm hmFr hmGm hFr hGm'
  exact ⟨Fr,Gm,Rf,Nf,hmFr,hmGm,hmRf,hmNf,hiRf,hiNf,hmMark,hMark,hRa,hNa,hiGm,hFrPrefix,hsGm,hTotal⟩
end SHE.ActualGaussianFullFamily
