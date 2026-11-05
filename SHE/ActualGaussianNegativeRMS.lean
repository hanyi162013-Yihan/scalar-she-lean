module
import all SHE.ActualGaussianFiniteRMS
public import SHE.ActualGaussianFiniteRMS
public import SHE.ActualTerminalRMS
import all SHE.ActualGaussianFirstMarkCaps
public import SHE.ActualGaussianFirstMarkCaps
public import SHE.SelectedHigherGaussianPrefixes
public import SHE.SelectedReferenceGaussianPrefixes
public import SHE.FullOrdinaryPrefixEnergy
public import SHE.CanonicalGaussianTerminalLeafRMS
public import SHE.FullFiniteGaussianLeafCap
import all SHE.ActualGaussianFullFamily
public import SHE.ActualGaussianFullFamily
public import SHE.AbsoluteHilbertFinitePrefixes
public import SHE.FullFirstDefectBandPrefixes
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
namespace SHE.ActualGaussianNegativeRMS
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

local notation "Cmark" hM:max ηmark:max=>DefectGapFiniteCoefficient.constant P
  (ControlledOldIntervals.fraction P*P.lower) (PhysicalScoreChain.uniformConstant 1)
  (ScalarHeatBandBernstein.amplitude D.cap D.holderConstant P.exponent N) ηmark N
    (fun i=>ControlledDefectConstants.constant ell M hell hM ρ hρ hρhalf i P)
local notation "MarkBound" hM:max ηmark:max=>sqrt (Cmark hM ηmark)*DefectGapFiniteCoefficient.clock Λ ρ*
  StateBands.geometricConstant (P.exponent-ηmark)*((2:ℝ)^(Jbase+1))^(-(P.exponent-ηmark))*sqrt (Neg ρ).toReal

local notation "RCap"=>ActualGaussianFiniteRMS.referenceCap
  (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
  (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (D:=D) (hT:=hT) (hT1:=hT1) (hsmall:=hsmall) (Jbase:=Jbase)
  (ρ:=ρ) (χref:=χref) (εref:=εref) (ηref:=ηref) (p:=p) (Bword:=Bword) (Bref:=Bref)
local notation "HCap"=>ActualGaussianFiniteRMS.higherCap
  (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
  (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (D:=D) (hT:=hT) (hT1:=hT1) (hsmall:=hsmall) (Jbase:=Jbase)
  (ρ:=ρ) (χ:=χ) (η:=η) (ε:=ε) (tail:=tail) (ζ:=ζ) (hρ:=hρ) (hρhalf:=hρhalf)
  (hχ0:=hχ0) (hχ1:=hχ1) (hm:=hm) (hα:=hα) (hαhalf:=hαhalf) (hζ:=hζ)
  (p:=p) (Bcur:=Bcur) (Bword:=Bword)
local notation "Terminal" j:max=>ActualTerminalBandField.value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S (a:=D.smoothCoefficient n) (Jbase+j) hL hρ
local notation "Error" j:max=>FullFiniteGaussianRMS.error
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP haD Jbase hL hρ N j
local notation "Leaf" j:max=>FullFiniteGaussianRMS.leaf
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP haD Jbase hL hρ N j

include hAs hχ0 hχ1 hm hα hαhalf hζ hχref hχref1 hεref hεrefhalf hηref hp
  hIJ₀ hIJ₁ hJ hκP hH hnull hBI0 hBI1 hB16 hBDGpast hlocalI hBDGnext hFstop hBDG4 hBDG8
  hJH hJP hJF hJC hJS hJG hβsmall hρeq in
/-- True original negative-input RMS form of the actual finite stochastic comparison. -/
theorem negative_rms(hActual:P.coefficient=(fun z=>κ+aV z))(hCanonical:P=Smooth n)
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
    (hfreq:Λ^(1/4:ℝ)≤(2:ℝ)^(Jbase+1))
    (hM:0≤M)(ηmark:ℝ)(hηmark:0<ηmark)(hηmarkβ:ηmark<P.exponent)
    (hAge:∀k,k≤N→(RemainderBandSpans.span P.exponent (Jbase+1):ℝ)≤
      ControlledDefectConstants.horizon P.lower P.lower_pos ell M hell hM ρ hρ hρhalf k)
    (hOld:∀r,r<N+1→(RemainderBandSpans.span P.exponent (Jbase+1):ℝ)≤PhysicalScoreChain.uniformHorizon 1 r)
    (hqr:∀k,k<N→∀i:Fin 3,0<MixedNativeReferenceGaussianFamily.degrees D.beta ρ εref ηref (k+1) i)
    (hqh:∀i:Fin 4,0<NativeFullRateCap.degree (NativeBandFrequencyRates.currentDegree D.beta ρ χ ζ)
      (NativeBandFrequencyRates.pastDegree D.beta ζ) (SignedNativeBandFrequency.goodDegree D.beta ε ζ)
      (SignedNativeBandFrequency.badDegree D.beta tail ζ) i)
    (hUeq:aU=D.residualCoefficient)(hVeq:aV=D.smoothCoefficient n)
    (Berror:ℕ→ℝ≥0)(hBDGerror:∀k,k<N+1→StandardTerminalBDGPower (k+2) J (Berror k))
    (hdepth:SHE.depth P.exponent≤N+1)
    (ηleaf:ℝ)(hηleaf:0<ηleaf)(hηleafβ:ηleaf≤P.exponent/4)
    (leafOrder:ℕ)(hleafOrder:0<leafOrder)
    (hoLeaf0:1≤(leafOrder:ℝ)*(1-P.exponent/2))
    (hoLeaf1:1≤(leafOrder:ℝ)*(1-(P.exponent/2)/P.exponent))
    (Bleaf Bcov:ℝ≥0)
    (hBDGleaf:StandardTerminalBDGPower (leafOrder*((N+1)+2)) J Bleaf)
    (hBDGcov:StandardTerminalBDGPower (N+3) J Bcov):
    let Cleaf:=FullRemainderConstants.comparison Rough κ M (H:ℝ) (N+1) (P.exponent/2) ηleaf leafOrder Bleaf B1 Bcov
    let LeafBound:=Λ^(-ρ/2)*sqrt Cleaf*CanonicalGaussianRootBands.amplitude D 1 (N+2)*
      (2:ℝ)^(D.beta/2+ηleaf)*(16/15:ℝ)*((2:ℝ)^(Jbase+1))^(-4:ℝ)*Global^((P.exponent/2)/2)
    ∀L:ℕ,sqrt (Neg ρ).toReal≤
      ((ScalarHeatBandBernstein.amplitude D.cap D.holderConstant D.beta 1*LowBands.lowBandConstant D.beta)*
        Λ^(-ρ/2))*((2:ℝ)^Jbase)^(1-D.beta)*sqrt Global+
      (FrBound+GmBound+(∑k∈Finset.range N,RCap k)+(∑k∈Finset.range N,HCap k)+MarkBound hM ηmark+
        sqrt (∫z,‖∑j∈Finset.range L,(Error j) z‖^2 ∂energyMeasure μ H)+LeafBound)+
      ActualTerminalReconstructionEnergy.error D n Jbase L:=by
  intro Cleaf LeafBound
  have hcmp:=ActualGaussianFiniteRMS.rms_le
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
    (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (haP:=haP) (D:=D) (hT:=hT) (hT1:=hT1) (hsmall:=hsmall) (n:=n)
    (J:=J) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (hnull:=hnull) (hJ:=hJ) (hAs:=hAs) (N:=N) (Jbase:=Jbase)
    (ρ:=ρ) (χ:=χ) (χref:=χref) (η:=η) (ε:=ε) (tail:=tail) (ζ:=ζ) (εref:=εref) (ηref:=ηref)
    (hρ:=hρ) (hχ0:=hχ0) (hχ1:=hχ1) (hm:=hm) (hα:=hα) (hαhalf:=hαhalf) (hζ:=hζ)
    (hχref:=hχref) (hχref1:=hχref1) (hεref:=hεref) (hεrefhalf:=hεrefhalf) (hηref:=hηref)
    (p:=p) (hp:=hp) (Bcur:=Bcur) (Bword:=Bword) (Bref:=Bref) (hκP:=hκP) (hH:=hH) (hL:=hL) (hρhalf:=hρhalf)
    (BI0:=BI0) (BI1:=BI1) (B16:=B16) (hBI0:=hBI0) (hBI1:=hBI1) (hB16:=hB16) (hJH:=hJH)
    (Bpast:=Bpast) (hBDGpast:=hBDGpast) (hlocalI:=hlocalI) (Bnext:=Bnext) (hBDGnext:=hBDGnext)
    (hFstop:=hFstop) (B4:=B4) (B8:=B8) (hBDG4:=hBDG4) (hBDG8:=hBDG8)
    (hβsmall:=hβsmall) (hρeq:=hρeq) (hJP:=hJP) (hJF:=hJF) (hJC:=hJC) (hJS:=hJS) (hJG:=hJG)
    hActual hCanonical hlocal hHpos hsmallProfile hsmallL2 B1 hBDG1 hBDGcur hBDGword hBDGref
    horder horderref htail hη hJbase hfreq hM ηmark hηmark hηmarkβ hAge hOld hqr hqh hUeq hVeq
    Berror hBDGerror hdepth ηleaf hηleaf hηleafβ leafOrder hleafOrder hoLeaf0 hoLeaf1 Bleaf Bcov hBDGleaf hBDGcov
  have hβeq:P.exponent=D.beta:=by rw [hCanonical];rfl
  have hβ:D.beta<1:=by rw [←hβeq];linarith only [hβsmall]
  intro L
  have hrec:=ActualTerminalRMS.reconstruct
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ J hIJ₀ hIJ₁
    hUeq hVeq hβ hH B1 hBDG1 Jbase L (by
      simpa only [ActualTerminalReconstruction.terminal] using (hcmp L).1)
  simp only [ActualTerminalReconstruction.terminal] at hrec
  exact hrec.trans (add_le_add (add_le_add (le_refl _) (hcmp L).2) (le_refl _))

end SHE.ActualGaussianNegativeRMS
