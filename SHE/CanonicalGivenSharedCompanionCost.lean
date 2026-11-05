module
import all SHE.ActualGaussianSharedCompanionDiagonal
public import SHE.ActualGaussianSharedCompanionDiagonal
public import SHE.CanonicalGivenCompanionFamily
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
namespace SHE.CanonicalGivenSharedCompanionCost
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
variable (𝓕:∀i,Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω i)))(μ:∀i,Measure (Ω i))[∀i,IsProbabilityMeasure (μ i)](h:ℝ≥0)(hh:(h:ℝ)≤1)(hpos:0<h)
local notation "Hor"=>NativeClock.rate*h
local notation "NativeFil" i:max=>PredictableTimeDilation.filtration (𝓕 i)
  (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)
variable (D:SmoothApproximation.ScalarData)(κ:ℝ)(hκ:0<κ)
  (hκD:κ=(ScalarReduction.additiveAmplitude D.lower)^2)
variable (I₀ I₁:∀i,StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (μ i) (NativeClock.rate*h))(u₀:ι→RealL2)
variable (J:∀i,StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (μ i) (NativeClock.rate*h))
  (hIJ₀:∀i,StandardScalarNaturality (I₀ i) (leftIntegral (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (μ i) (NativeClock.rate*h) (J i)))
  (hIJ₁:∀i,StandardScalarNaturality (I₁ i) (rightIntegral (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (μ i) (NativeClock.rate*h) (J i)))
  (hnull:∀i,NullCompleteFiltration.ContainsNullSets (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (μ i))
  (hJ:∀i,StandardFiniteIto.Universal (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (μ i) (NativeClock.rate*h) (J i))
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
variable (S:∀i k n,MixedNativeAdditiveResidualPair.Solution (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (μ i) (NativeClock.rate*h) (Λ k) κ hκ
  D.residual_continuous.measurable ((D.smooth_boundedSmooth n).smooth.continuous.measurable)
  D.ell_pos D.residual_bounds (D.smooth_bounds n) (I₀ i) (I₁ i) (u₀ i) (u₀ i))
local notation "Global" SS:max i:max k:max n:max=>MixedMovingEnergy.globalEnergy (NativeFil i) (μ i) Hor (Λ k) κ hκ Umeas (Vmeas n)
  D.ell_pos D.residual_bounds (D.smooth_bounds n) (I₀ i) (I₁ i) (u₀ i) (SS i k n)
local notation "Neg" i:max k:max n:max ρ:max=>MixedActualEnergyBridge.negativeEnergy (NativeFil i) (μ i) Hor (Λ k) κ hκ Umeas (Vmeas n)
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
variable (hHpos:0<(NativeClock.rate*h))(hH:((NativeClock.rate*h):ℝ)≤1)
  (hsmallProfile:∀n,ProfileStability.memoryConstant (ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall n).lower (ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall n).holder (ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall n).exponent*
    ProfileVolterra.powerConstant (((ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall n).exponent-2)/4)*(ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall n).horizon^((ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall n).exponent/4)≤1/2)
  (hsmallL2:∀n,ProfileStability.memoryConstant (ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall n).lower (ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall n).holder (ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall n).exponent*
    ProfileVolterra.powerConstant (((ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall n).exponent-1)/4)*(ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall n).horizon^((ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall n).exponent/4)≤1/2)
  (hcut:∀k,CommonComparisonCutoff.Ready D.ell D.cap D.ell_pos D.cap_nonneg ρ hρ hρhalf D hT hT1 hsmall (NativeClock.rate*h) hHpos (N+1) (cut k))
  (hfreq:∀k,(Λ k)^(1/4:ℝ)≤(2:ℝ)^(cut k+1))
  (hlow:∀k,(2:ℝ)^(cut k)≤2*(Λ k)^(1/4:ℝ))

include hκD in
theorem positiveProfile(n:ℕ):κ<(Smooth n).lower:=by
  change κ<(TotalSmoothLimit.amplitude D)^2+D.ell
  rw [hκD]
  change (ScalarReduction.additiveAmplitude D.lower)^2<(ScalarReduction.additiveAmplitude D.lower)^2+D.ell
  linarith [D.ell_pos]
local notation "FloorPos" n:max=>positiveProfile D κ hκD hT hT1 hsmall n
local notation "C0" i:max=>ActualGaussianMasterBound.constant (Ω:=(Ω i)) (H:=Hor) (κ:=κ) (ell:=D.ell) (M:=D.cap) (hell:=D.ell_pos)
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
  (𝓕:=(NativeFil i)) (μ:=(μ i)) (H:=Hor) (Λ:=Λ k) (κ:=κ) (hκ:=hκ) (haU:=Umeas) (haV:=Vmeas n)
  (hell:=D.ell_pos) (hbU:=D.residual_bounds) (hbV:=D.smooth_bounds n) (I₀:=(I₀ i)) (I₁:=(I₁ i)) (u₀:=(u₀ i)) (S:=(S i) k n)
  (P:=Smooth n) (haP:=Pbnd n) (D:=D) (n:=n) (Jbase:=cut k) (hL:=hΛ1 k) (hρ:=hρ) (N:=N)
local notation "Budget" i:max k:max=>ActualGaussianCompanionAttachment.ordinaryBudget
  (D:=D) (hT:=hT) (hT1:=hT1) (hsmall:=hsmall) (κ:=κ) (M:=D.cap) (H:=Hor)
  (Λ:=Λ k) (ρ:=ρ) (N:=N) (Jbase:=cut k) (Berror i)

variable (U:∀i,NativeFirstMildData.Data (𝓕 i) (μ i) h ((ScalarReduction.additiveAmplitude D.lower)^2)
  (CanonicalFixedHorizonCompanions.additive_pos D) D.residual_continuous.measurable D.ell_pos
  D.residual_bounds (I₀ i) (I₁ i) (u₀ i))

include hh hpos N ρ χ χref η ε tail ζ εref ηref hρ hρhalf hχ0 hχ1 hm hα hαhalf hζ p Bcur Bword Bref
  hκD hIJ₀ hIJ₁ hnull hJ hlocal hlocalI hFstop hHpos hH hsmallProfile hsmallL2 hcut hfreq hlow
  hχref hχref1 hεref hεrefhalf hηref hp hη hηmark hηmarkβ hηleaf hηleafβ hleafOrder hoLeaf0 hoLeaf1 hdepth
  hBI0 hBI1 hB16 hBDGpast hBDGnext hBDG4 hBDG8 hBDG1 hBDGcur hBDGword hBDGref hBDGerror hBDGleaf hBDGcov
  horder horderref htail hρeq hχeq hχrefeq hεrefeq hηrefeq hqh hqr hbad hΛ hΛ1 in
/-- The shared vanishing-cost diagonal is constructed from the GIVEN
rough original solutions. No companion-family or stochastic-master
premise remains; every rough first path is preserved exactly. -/
theorem exists_diagonal:
    ∃SS:∀i k n,MixedNativeAdditiveResidualPair.Solution (NativeFil i) (μ i) Hor (Λ k) κ hκ
      D.residual_continuous.measurable ((D.smooth_boundedSmooth n).smooth.continuous.measurable)
      D.ell_pos D.residual_bounds (D.smooth_bounds n) (I₀ i) (I₁ i) (u₀ i) (u₀ i),
      (∀i k n,(SS i k n).first=(U i).value) ∧
      ∃L index:ℕ→ℕ,StrictMono index ∧ Tendsto index atTop atTop ∧
        (∀k,0<L k ∧ SmoothReferenceLimit.error D (index k)<(Λ k)^(-2:ℝ)/2) ∧
        ∀i:ι,Tendsto (fun k=>(Λ k)^2*Global SS i k (index k)) atTop (𝓝 0) ∧
          Tendsto (fun k=>Global SS i k (index k)) atTop (𝓝 0):=by
  subst κ
  obtain ⟨SS,hSS⟩:=CanonicalGivenCompanionFamily.exists_family Ω 𝓕 μ h hh hpos D I₀ I₁ hnull
    BI0 BI1 hBI0 hBI1 u₀ U Λ (fun k=>zero_le_one.trans (hΛ1 k))
  refine ⟨SS,hSS,?_⟩
  exact ActualGaussianSharedCompanionDiagonal.exists_diagonal
    (𝓕:=fun i=>NativeFil i) (H:=Hor) (κ:=(ScalarReduction.additiveAmplitude D.lower)^2) (hκD:=rfl) (S:=SS)
    (Ω:=Ω) (μ:=μ) (D:=D) (hκ:=hκ) (I₀:=I₀) (I₁:=I₁)
    (u₀:=u₀) (J:=J) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (hnull:=hnull) (hJ:=hJ)
    (hlocal:=hlocal) (hlocalI:=hlocalI) (hFstop:=hFstop) (hT:=hT) (hT1:=hT1) (hsmall:=hsmall)
    (Λ:=Λ) (hΛ1:=hΛ1) (hΛ:=hΛ) (cut:=cut) (N:=N) (ρ:=ρ)
    (χ:=χ) (χref:=χref) (η:=η) (ε:=ε) (tail:=tail) (ζ:=ζ)
    (εref:=εref) (ηref:=ηref) (hρ:=hρ) (hρhalf:=hρhalf) (hρeq:=hρeq) (hχ0:=hχ0)
    (hχ1:=hχ1) (hm:=hm) (hχeq:=hχeq) (hα:=hα) (hαhalf:=hαhalf) (hζ:=hζ)
    (hη:=hη) (hχref:=hχref) (hχref1:=hχref1) (hεref:=hεref) (hεrefhalf:=hεrefhalf) (hηref:=hηref)
    (hχrefeq:=hχrefeq) (hεrefeq:=hεrefeq) (hηrefeq:=hηrefeq) (p:=p) (hp:=hp) (Bcur:=Bcur)
    (Bword:=Bword) (Bref:=Bref) (Berror:=Berror) (horder:=horder) (horderref:=horderref) (htail:=htail)
    (ηmark:=ηmark) (hηmark:=hηmark) (hηmarkβ:=hηmarkβ) (ηleaf:=ηleaf) (hηleaf:=hηleaf) (hηleafβ:=hηleafβ)
    (leafOrder:=leafOrder) (hleafOrder:=hleafOrder) (hoLeaf0:=hoLeaf0) (hoLeaf1:=hoLeaf1) (hdepth:=hdepth) (BI0:=BI0)
    (BI1:=BI1) (B16:=B16) (Bpast:=Bpast) (Bnext:=Bnext) (B4:=B4) (B8:=B8)
    (B1:=B1) (Bleaf:=Bleaf) (Bcov:=Bcov) (hBI0:=hBI0) (hBI1:=hBI1) (hB16:=hB16)
    (hBDGpast:=hBDGpast) (hBDGnext:=hBDGnext) (hBDG4:=hBDG4) (hBDG8:=hBDG8) (hBDG1:=hBDG1) (hBDGcur:=hBDGcur)
    (hBDGword:=hBDGword) (hBDGref:=hBDGref) (hBDGerror:=hBDGerror) (hBDGleaf:=hBDGleaf) (hBDGcov:=hBDGcov) (hqh:=hqh)
    (hbad:=hbad) (hqr:=hqr) (hHpos:=hHpos) (hH:=hH) (hsmallProfile:=hsmallProfile) (hsmallL2:=hsmallL2)
    (hcut:=hcut) (hfreq:=hfreq) (hlow:=hlow)
end SHE.CanonicalGivenSharedCompanionCost
