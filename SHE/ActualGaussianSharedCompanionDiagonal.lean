module
import all SHE.ActualGaussianCompanionUniform
public import SHE.ActualGaussianCompanionUniform
import all SHE.ActualGaussianCompanionAttachment
public import SHE.ActualGaussianCompanionAttachment
public import SHE.CommonComparisonCutoff
public import SHE.CanonicalCompanionExpansion
import all SHE.ActualGaussianMasterBound
public import SHE.ActualGaussianMasterBound
public import SHE.SharedCompanionCostLimit
import all SHE.ActualGaussianNegativeRMS
public import SHE.ActualGaussianNegativeRMS
public import SHE.ActualGaussianBaseCoefficient
public import SHE.ActualGaussianRateFolding
public import SHE.ActualReferenceRateFolding
public import SHE.ActualGaussianMarkCoefficient
public import SHE.NativeMasterRHSCombination
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
namespace SHE.ActualGaussianSharedCompanionDiagonal
open Filter Topology
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

open PastItoInputs PastItoAlgebra PhysicalProfile Real AddCircle Set WordRecursion ControlledProfile
  ControlledReferenceLevel SmoothCylinders UniformSmooth CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalScoreChain PhysicalChainArrays PhysicalParentGeometry ProfileStability ProfileL2
open scoped BigOperators
local instance :Fact (0<2*Real.pi):=⟨by positivity⟩
local instance :SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology

variable {ι:Type}[Fintype ι](Ω:ι→Type)[∀i,MeasurableSpace (Ω i)]
variable (𝓕:∀i,Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω i)))(μ:∀i,Measure (Ω i))[∀i,IsProbabilityMeasure (μ i)](H:ℝ≥0)
variable (D:SmoothApproximation.ScalarData)(κ:ℝ)(hκ:0<κ)
  (hκD:κ=(ScalarReduction.additiveAmplitude D.lower)^2)
variable (I₀ I₁:∀i,StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) (𝓕 i) (μ i) H)(u₀:ι→RealL2)
variable (J:∀i,StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) (𝓕 i) (μ i) H)
  (hIJ₀:∀i,StandardScalarNaturality (I₀ i) (leftIntegral (𝓕 i) (μ i) H (J i)))
  (hIJ₁:∀i,StandardScalarNaturality (I₁ i) (rightIntegral (𝓕 i) (μ i) H (J i)))
  (hnull:∀i,NullCompleteFiltration.ContainsNullSets (𝓕 i) (μ i))
  (hJ:∀i,StandardFiniteIto.Universal (𝓕 i) (μ i) H (J i))
  (hlocal:∀i,StandardTerminalPastLocality (J i))(hlocalI:∀i,StandardTerminalPastLocality (I₁ i))
  (hFstop:∀i,StandardItoStoppedParameterFubini (J i))
variable {T:ℝ}(hT:0<T)(hT1:T≤1)
  (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2)
local notation "Smooth"=>ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall
local notation "Pzero"=>Smooth 0
local notation "Umeas"=>D.residual_continuous.measurable
local notation "Vmeas" n:max=>(D.smooth_boundedSmooth n).smooth.continuous.measurable
local notation "Pbnd" n:max=>SmoothComparisonParameters.smooth_bounded D hT hT1 hsmall n
local notation "TotalBnd" n:max=>CanonicalCompanionExpansion.total_boundedSmooth D n κ rfl
variable (Λ:ℕ→ℝ)(hΛ1:∀k,1≤Λ k)(hΛ:Tendsto Λ atTop atTop)(cut:ℕ→ℕ)
variable (S:∀i k n,MixedNativeAdditiveResidualPair.Solution (𝓕 i) (μ i) H (Λ k) κ hκ
  D.residual_continuous.measurable ((D.smooth_boundedSmooth n).smooth.continuous.measurable)
  D.ell_pos D.residual_bounds (D.smooth_bounds n) (I₀ i) (I₁ i) (u₀ i) (u₀ i))
local notation "Global" i:max k:max n:max=>MixedMovingEnergy.globalEnergy (𝓕 i) (μ i) H (Λ k) κ hκ Umeas (Vmeas n)
  D.ell_pos D.residual_bounds (D.smooth_bounds n) (I₀ i) (I₁ i) (u₀ i) (S i k n)
local notation "Neg" i:max k:max n:max ρ:max=>MixedActualEnergyBridge.negativeEnergy (𝓕 i) (μ i) H (Λ k) κ hκ Umeas (Vmeas n)
  D.ell_pos D.residual_bounds (D.smooth_bounds n) (I₀ i) (I₁ i) (u₀ i) (S i k n) ρ
variable (N:ℕ)(ρ χ χref η ε tail ζ εref ηref:ℝ)
  (hρ:0<ρ)(hρhalf:ρ<1/2)(hρeq:ρ=SHE.rho D.beta)
  (hχ0:0≤χ)(hχ1:χ<1)(hm:χ<D.beta+2*ρ)(hχeq:χ=SHE.chi D.beta)
  (hα:0<ρ+η)(hαhalf:ρ+η<1/2)(hζ:0<ζ)(hη:0<η)
  (hχref:0<χref)(hχref1:χref<1)(hεref:0≤εref)(hεrefhalf:εref<1/2)(hηref:0<ηref)
  (hχrefeq:χref=ActualReferenceMasterClosure.referenceExponent D.beta)
  (hεrefeq:εref=D.beta/100)(hηrefeq:ηref=D.beta/100)
  (p:ℕ)(hp:0<p)(Bcur Bword Bref Berror:ι→ℕ→ℝ≥0)
  (horder:1≤(p:ℝ)*(1-χ))(horderref:1≤(p:ℝ)*(1-χref))
  (htail:tail≤ε*(2*((p-1:ℕ):ℝ)))
  (ηmark:ℝ)(hηmark:0<ηmark)(hηmarkβ:ηmark<D.beta)
  (ηleaf:ℝ)(hηleaf:0<ηleaf)(hηleafβ:ηleaf≤D.beta/4)
  (leafOrder:ℕ)(hleafOrder:0<leafOrder)
  (hoLeaf0:1≤(leafOrder:ℝ)*(1-D.beta/2))
  (hoLeaf1:1≤(leafOrder:ℝ)*(1-(D.beta/2)/D.beta))
  (hdepth:SHE.depth D.beta≤N+1)
variable (BI0 BI1 B16 Bpast Bnext B4 B8 B1 Bleaf Bcov:ι→ℝ≥0)
  (hBI0:∀i,StandardTerminalBDG16 (I₀ i) (BI0 i))(hBI1:∀i,StandardTerminalBDG16 (I₁ i) (BI1 i))(hB16:∀i,StandardTerminalBDG16 (J i) (B16 i))
  (hBDGpast:∀i,StandardTerminalBDGPower 2 (J i) (Bpast i))(hBDGnext:∀i,StandardTerminalBDGPower 1 (I₁ i) (Bnext i))
  (hBDG4:∀i,StandardTerminalBDGPower 4 (J i) (B4 i))(hBDG8:∀i,StandardTerminalBDGPower 8 (J i) (B8 i))
  (hBDG1:∀i,StandardTerminalBDGPower 1 (J i) (B1 i))
  (hBDGcur:∀i,∀k,k<N→StandardTerminalBDGPower (p*(k+3)) (J i) ((Bcur i) k))
  (hBDGword:∀i,∀k,k<N→StandardTerminalBDGPower (k+3) (J i) ((Bword i) k))
  (hBDGref:∀i,∀k,k<N→StandardTerminalBDGPower ((2*p)*(k+3)) (J i) ((Bref i) k))
  (hBDGerror:∀i,∀k,k<N+1→StandardTerminalBDGPower (k+2) (J i) ((Berror i) k))
  (hBDGleaf:∀i,StandardTerminalBDGPower (leafOrder*((N+1)+2)) (J i) (Bleaf i))
  (hBDGcov:∀i,StandardTerminalBDGPower (N+3) (J i) (Bcov i))
local notation "HQ"=>NativeFullRateCap.degree (NativeBandFrequencyRates.currentDegree D.beta ρ χ ζ)
  (NativeBandFrequencyRates.pastDegree D.beta ζ) (SignedNativeBandFrequency.goodDegree D.beta ε ζ)
  (SignedNativeBandFrequency.badDegree D.beta tail ζ)
variable (hqh:∀i:Fin 4,0<NativeFullRateCap.degree (NativeBandFrequencyRates.currentDegree D.beta ρ χ ζ)
  (NativeBandFrequencyRates.pastDegree D.beta ζ) (SignedNativeBandFrequency.goodDegree D.beta ε ζ)
  (SignedNativeBandFrequency.badDegree D.beta tail ζ) i)
  (hbad:16<NativeFullRateCap.degree (NativeBandFrequencyRates.currentDegree D.beta ρ χ ζ)
  (NativeBandFrequencyRates.pastDegree D.beta ζ) (SignedNativeBandFrequency.goodDegree D.beta ε ζ)
  (SignedNativeBandFrequency.badDegree D.beta tail ζ) 3)
  (hqr:∀k,k<N→∀i:Fin 3,0<MixedNativeReferenceGaussianFamily.degrees D.beta ρ εref ηref (k+1) i)
variable (hHpos:0<H)(hH:(H:ℝ)≤1)
  (hsmallProfile:∀n,ProfileStability.memoryConstant (ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall n).lower (ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall n).holder (ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall n).exponent*
    ProfileVolterra.powerConstant (((ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall n).exponent-2)/4)*(ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall n).horizon^((ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall n).exponent/4)≤1/2)
  (hsmallL2:∀n,ProfileStability.memoryConstant (ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall n).lower (ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall n).holder (ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall n).exponent*
    ProfileVolterra.powerConstant (((ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall n).exponent-1)/4)*(ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall n).horizon^((ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall n).exponent/4)≤1/2)
  (hcut:∀k,CommonComparisonCutoff.Ready D.ell D.cap D.ell_pos D.cap_nonneg ρ hρ hρhalf D hT hT1 hsmall H hHpos (N+1) (cut k))
  (hfreq:∀k,(Λ k)^(1/4:ℝ)≤(2:ℝ)^(cut k+1))
  (hlow:∀k,(2:ℝ)^(cut k)≤2*(Λ k)^(1/4:ℝ))

include hκD in
theorem positiveProfile(n:ℕ):κ<(Smooth n).lower:=by
  change κ<(TotalSmoothLimit.amplitude D)^2+D.ell
  rw [hκD]
  change (ScalarReduction.additiveAmplitude D.lower)^2<(ScalarReduction.additiveAmplitude D.lower)^2+D.ell
  linarith [D.ell_pos]
local notation "FloorPos" n:max=>positiveProfile D κ hκD hT hT1 hsmall n
local notation "C0" i:max=>ActualGaussianMasterBound.constant (Ω:=(Ω i)) (H:=H) (κ:=κ) (ell:=D.ell) (M:=D.cap) (hell:=D.ell_pos)
  (P:=Pzero) (hκP:=FloorPos 0) (D:=D) (hT:=hT) (hT1:=hT1) (hsmall:=hsmall) (N:=N)
  (ρ:=ρ) (χ:=χ) (η:=η) (ε:=ε) (tail:=tail) (ζ:=ζ) (hρ:=hρ) (hρhalf:=hρhalf)
  (hχ0:=hχ0) (hχ1:=hχ1) (hm:=hm) (hα:=hα) (hαhalf:=hαhalf) (hζ:=hζ)
  (p:=p) (Bcur:=(Bcur i)) (Bword:=(Bword i)) (Bref:=(Bref i)) (Bnext:=(Bnext i)) ηleaf leafOrder (Bleaf i) (B1 i) (Bcov i)
local notation "HC" i:max=>ActualGaussianMasterBound.higherConstant (Ω:=(Ω i)) (κ:=κ) (M:=D.cap) (hell:=D.ell_pos) (D:=D)
  (hT:=hT) (hT1:=hT1) (hsmall:=hsmall) (N:=N) (ρ:=ρ) (χ:=χ) (η:=η) (ε:=ε) (tail:=tail) (ζ:=ζ)
  (hρ:=hρ) (hρhalf:=hρhalf) (hχ0:=hχ0) (hχ1:=hχ1) (hm:=hm) (hα:=hα) (hαhalf:=hαhalf) (hζ:=hζ)
  (p:=p) (Bcur:=(Bcur i)) (Bword:=(Bword i))
local notation "AK"=>ActualGaussianMasterBound.linearK (ell:=D.ell) (M:=D.cap) (hell:=D.ell_pos) (D:=D)
  (hT:=hT) (hT1:=hT1) (hsmall:=hsmall) (N:=N) (ρ:=ρ) (χ:=χ) (ε:=ε) (tail:=tail) (ζ:=ζ)
  (hρ:=hρ) (hρhalf:=hρhalf) D.cap_nonneg ηmark
local notation "BM"=>ActualGaussianMasterBound.linearM (D:=D) (ρ:=ρ) (χ:=χ) (ε:=ε) (tail:=tail) (ζ:=ζ)
local notation "CE"=>ActualGaussianCompanionAttachment.energyConstant ρ (ell:=D.ell) (M:=D.cap)
local notation "Error" i:max k:max n:max=>ActualGaussianCompanionAttachment.ordinaryEnergy
  (𝓕:=(𝓕 i)) (μ:=(μ i)) (H:=H) (Λ:=Λ k) (κ:=κ) (hκ:=hκ) (haU:=Umeas) (haV:=Vmeas n)
  (hell:=D.ell_pos) (hbU:=D.residual_bounds) (hbV:=D.smooth_bounds n) (I₀:=(I₀ i)) (I₁:=(I₁ i)) (u₀:=(u₀ i)) (S:=(S i) k n)
  (P:=Smooth n) (haP:=Pbnd n) (D:=D) (n:=n) (Jbase:=cut k) (hL:=hΛ1 k) (hρ:=hρ) (N:=N)
local notation "Budget" i:max k:max=>ActualGaussianCompanionAttachment.ordinaryBudget
  (D:=D) (hT:=hT) (hT1:=hT1) (hsmall:=hsmall) (κ:=κ) (M:=D.cap) (H:=H)
  (Λ:=Λ k) (ρ:=ρ) (N:=N) (Jbase:=cut k) (Berror i)

include N ρ χ χref η ε tail ζ εref ηref hρ hρhalf hχ0 hχ1 hm hα hαhalf hζ p Bcur Bword Bref
  hκD hIJ₀ hIJ₁ hnull hJ hlocal hlocalI hFstop hHpos hH hsmallProfile hsmallL2 hcut hfreq hlow
  hχref hχref1 hεref hεrefhalf hηref hp hη hηmark hηmarkβ hηleaf hηleafβ hleafOrder hoLeaf0 hoLeaf1 hdepth
  hBI0 hBI1 hB16 hBDGpast hBDGnext hBDG4 hBDG8 hBDG1 hBDGcur hBDGword hBDGref hBDGerror hBDGleaf hBDGcov
  horder horderref htail hρeq hχeq hχrefeq hεrefeq hηrefeq hqh hqr hbad hΛ hΛ1 in
/-- A finite family of genuine original probability spaces shares ONE
strictly increasing canonical companion sequence. All stochastic bounds
are proved from each actual same-driver solution family. -/
theorem exists_diagonal:
    ∃L index:ℕ→ℕ,StrictMono index ∧ Tendsto index atTop atTop ∧
      (∀k,0<L k ∧ SmoothReferenceLimit.error D (index k)<(Λ k)^(-2:ℝ)/2) ∧
      ∀i:ι,Tendsto (fun k=>(Λ k)^2*Global i k (index k)) atTop (𝓝 0) ∧
        Tendsto (fun k=>Global i k (index k)) atTop (𝓝 0):=by
  classical
  have hc0(i:ι):0<C0 i:=ActualGaussianMasterBound.constant_pos (Ω:=Ω i) (P:=Pzero) (D:=D) (hT:=hT) (hT1:=hT1) (hsmall:=hsmall)
    (κ:=κ) (ell:=D.ell) (M:=D.cap) (H:=H) (hell:=D.ell_pos) (hκP:=FloorPos 0) (ρ:=ρ) (hρ:=hρ) (hρhalf:=hρhalf)
    (N:=N) (Bnext:=Bnext i) (χ:=χ) (η:=η) (ε:=ε) (tail:=tail) (ζ:=ζ)
    (hχ0:=hχ0) (hχ1:=hχ1) (hm:=hm) (hα:=hα) (hαhalf:=hαhalf) (hζ:=hζ)
    (p:=p) (Bcur:=Bcur i) (Bword:=Bword i) (Bref:=Bref i) ηleaf leafOrder (Bleaf i) (B1 i) (Bcov i) hqh
  let C:=1+∑i:ι,max (C0 i) CE
  have hn(i:ι):0≤max (C0 i) CE:=(hc0 i).le.trans (le_max_left _ _)
  have hs:0≤∑i:ι,max (C0 i) CE:=Finset.sum_nonneg (fun i _=>hn i)
  have hC:0≤C:=by dsimp only [C];linarith
  have hCi(i:ι):max (C0 i) CE≤C:=by
    have hh:=Finset.single_le_sum (fun j _=>hn j) (Finset.mem_univ i)
    dsimp only [C]
    linarith only [hh]
  have facts(i:ι)(k n:ℕ):
      sqrt (Global i k n)≤C*energyScale D.beta (Λ k)*sqrt (Neg i k n ρ).toReal ∧
      ∀L:ℕ,(Error i k n) L≤(ScalarApproximationDiscrepancy.scalarError D n)^2*(Budget i k) L ∧
        ActualReferenceMasterClosure.Bound D.beta C (Λ k) (sqrt (Neg i k n ρ).toReal) (sqrt (Global i k n))
          (sqrt ((Error i k n) L)+ActualTerminalReconstructionEnergy.error D n (cut k) L+(HC i)*(Λ k)^(-(HQ 3/8)))
          (AK (Λ k)) (BM (Λ k)) 0 0:=by
    have hr:=(hcut k).2 n (cut k+1) (by omega)
    have hJH:=hr.1
    have hJP:=hr.2.1
    have hOld:=hr.2.2.1
    have hAge(i:ℕ)(hi:i≤N): (RemainderBandSpans.span (Smooth n).exponent (cut k+1):ℝ)≤
        ControlledDefectConstants.horizon (Smooth n).lower (Smooth n).lower_pos D.ell D.cap D.ell_pos D.cap_nonneg ρ hρ hρhalf i:=
      hr.2.2.2.1 i (by omega)
    have hJF:=hr.2.2.2.2.1
    have hJC:=hr.2.2.2.2.2.1
    have hJS:=hr.2.2.2.2.2.2.1
    have hJG:=hr.2.2.2.2.2.2.2
    have hJbase:FiniteNativeGaussianCutoff.index D hT hT1 hsmall H hHpos N≤cut k:=by
      apply le_trans ?_ (hcut k).1
      unfold FiniteNativeGaussianCutoff.index
      apply Finset.sup_le
      intro i _
      exact FiniteNativeGaussianCutoff.le_index_of_pos D hT hT1 hsmall H hHpos (N+1) (i+1) (by omega) (by omega)
    have hpkg:=ActualGaussianCompanionAttachment.actual
      (𝓕:=(𝓕 i)) (μ:=(μ i)) (H:=H) (Λ:=Λ k) (κ:=κ) (hκ:=hκ) (haU:=Umeas) (haV:=Vmeas n) (hell:=D.ell_pos) (hbU:=D.residual_bounds) (hbV:=D.smooth_bounds n)
      (I₀:=(I₀ i)) (I₁:=(I₁ i)) (u₀:=(u₀ i)) (S:=(S i) k n) (P:=Smooth n) (haP:=Pbnd n) (D:=D) (hT:=hT) (hT1:=hT1) (hsmall:=hsmall) (n:=n)
      (J:=(J i)) (hIJ₀:=(hIJ₀ i)) (hIJ₁:=(hIJ₁ i)) (hnull:=(hnull i)) (hJ:=(hJ i)) (hAs:=TotalBnd n) (N:=N) (Jbase:=cut k)
      (ρ:=ρ) (χ:=χ) (χref:=χref) (η:=η) (ε:=ε) (tail:=tail) (ζ:=ζ) (εref:=εref) (ηref:=ηref)
      (hρ:=hρ) (hχ0:=hχ0) (hχ1:=hχ1) (hm:=hm) (hα:=hα) (hαhalf:=hαhalf) (hζ:=hζ)
      (hχref:=hχref) (hχref1:=hχref1) (hεref:=hεref) (hεrefhalf:=hεrefhalf) (hηref:=hηref)
      (p:=p) (hp:=hp) (Bcur:=(Bcur i)) (Bword:=(Bword i)) (Bref:=(Bref i)) (hκP:=FloorPos n) (hH:=hH) (hL:=hΛ1 k) (hρhalf:=hρhalf)
      (BI0:=(BI0 i)) (BI1:=(BI1 i)) (B16:=(B16 i)) (hBI0:=(hBI0 i)) (hBI1:=(hBI1 i)) (hB16:=(hB16 i)) (hJH:=hJH)
      (Bpast:=(Bpast i)) (hBDGpast:=(hBDGpast i)) (hlocalI:=(hlocalI i)) (Bnext:=(Bnext i)) (hBDGnext:=(hBDGnext i))
      (hFstop:=(hFstop i)) (B4:=(B4 i)) (B8:=(B8 i)) (hBDG4:=(hBDG4 i)) (hBDG8:=(hBDG8 i))
      (hβsmall:=D.beta_le) (hρeq:=hρeq) (hJP:=hJP) (hJF:=hJF) (hJC:=hJC) (hJS:=hJS) (hJG:=hJG)
      (CanonicalCompanionExpansion.total_eq D n hT hT1 hsmall hκD rfl) rfl (hlocal i) hHpos (hsmallProfile n) (hsmallL2 n) (B1 i) (hBDG1 i) (hBDGcur i) (hBDGword i) (hBDGref i)
      horder horderref htail hη hJbase (hfreq k) D.cap_nonneg ηmark hηmark hηmarkβ hAge hOld hqr hqh rfl rfl
      (Berror i) (hBDGerror i) hdepth ηleaf hηleaf hηleafβ leafOrder hleafOrder hoLeaf0 hoLeaf1 (Bleaf i) (Bcov i) (hBDGleaf i) (hBDGcov i)
      hχeq hχrefeq hεrefeq hηrefeq (hlow k)

    have hc:=ActualGaussianMasterBound.constant_congr (Ω:=(Ω i)) (P:=Smooth n) (D:=D) (hT:=hT) (hT1:=hT1) (hsmall:=hsmall)
      (κ:=κ) (ell:=D.ell) (M:=D.cap) (H:=H) (hell:=D.ell_pos) (hκP:=FloorPos n) (ρ:=ρ) (hρ:=hρ) (hρhalf:=hρhalf)
      (N:=N) (Bnext:=(Bnext i)) (χ:=χ) (η:=η) (ε:=ε) (tail:=tail) (ζ:=ζ)
      (hχ0:=hχ0) (hχ1:=hχ1) (hm:=hm) (hα:=hα) (hαhalf:=hαhalf) (hζ:=hζ)
      (p:=p) (Bcur:=(Bcur i)) (Bword:=(Bword i)) (Bref:=(Bref i)) Pzero (FloorPos 0) rfl rfl rfl rfl ηleaf leafOrder (Bleaf i) (B1 i) (Bcov i)
    rw [hc] at hpkg

    have hci:max (C0 i) CE≤C:=hCi i
    refine ⟨hpkg.2.2.1.trans ?_,?_⟩
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hci (rpow_nonneg (zero_le_one.trans (hΛ1 k)) _)) (sqrt_nonneg _)
    · intro L
      refine ⟨(hpkg.2.2.2 L).2.1,?_⟩
      exact SharedCompanionCostLimit.bound_mono (zero_le_one.trans (hΛ1 k)) (sqrt_nonneg _) (sqrt_nonneg _)
        (ActualGaussianMasterBound.linearK_nonneg (D:=D) (hT:=hT) (hT1:=hT1) (hsmall:=hsmall)
          (ell:=D.ell) (M:=D.cap) (hell:=D.ell_pos) (ρ:=ρ) (hρ:=hρ) (hρhalf:=hρhalf) (N:=N)
          (χ:=χ) (ε:=ε) (tail:=tail) (ζ:=ζ) D.cap_nonneg ηmark (Λ k)
          (zero_le_one.trans (hΛ1 k)) hηmarkβ)
        (ActualGaussianMasterBound.linearM_nonneg (D:=D) (ρ:=ρ) (χ:=χ) (ε:=ε) (tail:=tail) (ζ:=ζ)
          (Λ k) (zero_le_one.trans (hΛ1 k))) hci (hpkg.2.2.2 L).2.2
  have ha:=ActualGaussianMasterBound.linearK_limit (D:=D) (hT:=hT) (hT1:=hT1) (hsmall:=hsmall)
    (ell:=D.ell) (M:=D.cap) (hell:=D.ell_pos) (ρ:=ρ) (hρ:=hρ) (hρhalf:=hρhalf) (N:=N)
    (χ:=χ) (ε:=ε) (tail:=tail) (ζ:=ζ) D.cap_nonneg ηmark hηmarkβ (hqh 2)
  have hb:=ActualGaussianMasterBound.scaled_linearM_limit (D:=D) (ρ:=ρ) (χ:=χ) (ε:=ε) (tail:=tail) (ζ:=ζ)
    D.beta_le (hqh 1)
  have hb0:∀ᶠmass:ℝ in atTop,0≤BM mass:=by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with mass hm
    exact ActualGaussianMasterBound.linearM_nonneg (D:=D) (ρ:=ρ) (χ:=χ) (ε:=ε) (tail:=tail) (ζ:=ζ) mass hm

  let K:ι→ℕ→ℕ→ℕ→ℝ:=fun i k _ n=>sqrt (Neg i k n ρ).toReal
  let m:ι→ℕ→ℕ→ℕ→ℝ:=fun i k _ n=>sqrt (Global i k n)
  let E:ι→ℕ→ℕ→ℕ→ℝ:=fun i k L n=>(Error i k n) L
  obtain ⟨L,index,hi,hit,happrox,hcost⟩:=SharedCompanionCostLimit.exists_diagonal D D.beta_le C hC HQ hbad
    (fun i=>HC i) (fun i k L=>(Budget i k) L) Λ hΛ1 hΛ cut AK BM ha hb hb0 K m E
    (fun i k L n _=>sqrt_nonneg _) (fun i k L n _=>sqrt_nonneg _)
    (fun i k L n _=>(facts i k n).1) (fun i k L n _=>((facts i k n).2 L).1)
    (fun i k L n _=>((facts i k n).2 L).2)
  refine ⟨L,index,hi,hit,happrox,?_⟩
  intro i
  constructor
  · have ht:=(hcost i).1
    convert! ht using 1
    funext k
    dsimp only [m]
    have hg:0≤Global i k (index k):=integral_nonneg (fun _=>sq_nonneg _)
    rw [sq_sqrt hg]
  · have ht:=(hcost i).2
    convert! ht using 1
    funext k
    dsimp only [m]
    have hg:0≤Global i k (index k):=integral_nonneg (fun _=>sq_nonneg _)
    rw [sq_sqrt hg]
end SHE.ActualGaussianSharedCompanionDiagonal
