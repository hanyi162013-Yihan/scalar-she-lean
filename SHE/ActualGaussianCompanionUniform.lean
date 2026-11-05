module
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
namespace SHE.ActualGaussianCompanionUniform
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
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (D:SmoothApproximation.ScalarData)(κ:ℝ)(hκ:0<κ)
  (hκD:κ=(ScalarReduction.additiveAmplitude D.lower)^2)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)(u₀:RealL2)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
  (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
  (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
  (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)(hJ:StandardFiniteIto.Universal 𝓕 μ H J)
  (hlocal:StandardTerminalPastLocality J)(hlocalI:StandardTerminalPastLocality I₁)
  (hFstop:StandardItoStoppedParameterFubini J)
variable {T:ℝ}(hT:0<T)(hT1:T≤1)
  (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2)
local notation "Smooth"=>ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall
local notation "Pzero"=>Smooth 0
local notation "Umeas"=>D.residual_continuous.measurable
local notation "Vmeas" n:max=>(D.smooth_boundedSmooth n).smooth.continuous.measurable
local notation "Pbnd" n:max=>SmoothComparisonParameters.smooth_bounded D hT hT1 hsmall n
local notation "TotalBnd" n:max=>CanonicalCompanionExpansion.total_boundedSmooth D n κ rfl
variable (Λ:ℕ→ℝ)(hΛ1:∀k,1≤Λ k)(hΛ:Tendsto Λ atTop atTop)(cut:ℕ→ℕ)
variable (S:∀k n:ℕ,MixedNativeAdditiveResidualPair.Solution 𝓕 μ H (Λ k) κ hκ D.residual_continuous.measurable ((D.smooth_boundedSmooth n).smooth.continuous.measurable)
  D.ell_pos D.residual_bounds (D.smooth_bounds n) I₀ I₁ u₀ u₀)
local notation "Global" k:max n:max=>MixedMovingEnergy.globalEnergy 𝓕 μ H (Λ k) κ hκ Umeas (Vmeas n)
  D.ell_pos D.residual_bounds (D.smooth_bounds n) I₀ I₁ u₀ (S k n)
local notation "Neg" k:max n:max ρ:max=>MixedActualEnergyBridge.negativeEnergy 𝓕 μ H (Λ k) κ hκ Umeas (Vmeas n)
  D.ell_pos D.residual_bounds (D.smooth_bounds n) I₀ I₁ u₀ (S k n) ρ
variable (N:ℕ)(ρ χ χref η ε tail ζ εref ηref:ℝ)
  (hρ:0<ρ)(hρhalf:ρ<1/2)(hρeq:ρ=SHE.rho D.beta)
  (hχ0:0≤χ)(hχ1:χ<1)(hm:χ<D.beta+2*ρ)(hχeq:χ=SHE.chi D.beta)
  (hα:0<ρ+η)(hαhalf:ρ+η<1/2)(hζ:0<ζ)(hη:0<η)
  (hχref:0<χref)(hχref1:χref<1)(hεref:0≤εref)(hεrefhalf:εref<1/2)(hηref:0<ηref)
  (hχrefeq:χref=ActualReferenceMasterClosure.referenceExponent D.beta)
  (hεrefeq:εref=D.beta/100)(hηrefeq:ηref=D.beta/100)
  (p:ℕ)(hp:0<p)(Bcur Bword Bref Berror:ℕ→ℝ≥0)
  (horder:1≤(p:ℝ)*(1-χ))(horderref:1≤(p:ℝ)*(1-χref))
  (htail:tail≤ε*(2*((p-1:ℕ):ℝ)))
  (ηmark:ℝ)(hηmark:0<ηmark)(hηmarkβ:ηmark<D.beta)
  (ηleaf:ℝ)(hηleaf:0<ηleaf)(hηleafβ:ηleaf≤D.beta/4)
  (leafOrder:ℕ)(hleafOrder:0<leafOrder)
  (hoLeaf0:1≤(leafOrder:ℝ)*(1-D.beta/2))
  (hoLeaf1:1≤(leafOrder:ℝ)*(1-(D.beta/2)/D.beta))
  (hdepth:SHE.depth D.beta≤N+1)
variable (BI0 BI1 B16 Bpast Bnext B4 B8 B1 Bleaf Bcov:ℝ≥0)
  (hBI0:StandardTerminalBDG16 I₀ BI0)(hBI1:StandardTerminalBDG16 I₁ BI1)(hB16:StandardTerminalBDG16 J B16)
  (hBDGpast:StandardTerminalBDGPower 2 J Bpast)(hBDGnext:StandardTerminalBDGPower 1 I₁ Bnext)
  (hBDG4:StandardTerminalBDGPower 4 J B4)(hBDG8:StandardTerminalBDGPower 8 J B8)
  (hBDG1:StandardTerminalBDGPower 1 J B1)
  (hBDGcur:∀k,k<N→StandardTerminalBDGPower (p*(k+3)) J (Bcur k))
  (hBDGword:∀k,k<N→StandardTerminalBDGPower (k+3) J (Bword k))
  (hBDGref:∀k,k<N→StandardTerminalBDGPower ((2*p)*(k+3)) J (Bref k))
  (hBDGerror:∀k,k<N+1→StandardTerminalBDGPower (k+2) J (Berror k))
  (hBDGleaf:StandardTerminalBDGPower (leafOrder*((N+1)+2)) J Bleaf)
  (hBDGcov:StandardTerminalBDGPower (N+3) J Bcov)
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
local notation "C0"=>ActualGaussianMasterBound.constant (Ω:=Ω) (H:=H) (κ:=κ) (ell:=D.ell) (M:=D.cap) (hell:=D.ell_pos)
  (P:=Pzero) (hκP:=FloorPos 0) (D:=D) (hT:=hT) (hT1:=hT1) (hsmall:=hsmall) (N:=N)
  (ρ:=ρ) (χ:=χ) (η:=η) (ε:=ε) (tail:=tail) (ζ:=ζ) (hρ:=hρ) (hρhalf:=hρhalf)
  (hχ0:=hχ0) (hχ1:=hχ1) (hm:=hm) (hα:=hα) (hαhalf:=hαhalf) (hζ:=hζ)
  (p:=p) (Bcur:=Bcur) (Bword:=Bword) (Bref:=Bref) (Bnext:=Bnext) ηleaf leafOrder Bleaf B1 Bcov
local notation "HC"=>ActualGaussianMasterBound.higherConstant (Ω:=Ω) (κ:=κ) (M:=D.cap) (hell:=D.ell_pos) (D:=D)
  (hT:=hT) (hT1:=hT1) (hsmall:=hsmall) (N:=N) (ρ:=ρ) (χ:=χ) (η:=η) (ε:=ε) (tail:=tail) (ζ:=ζ)
  (hρ:=hρ) (hρhalf:=hρhalf) (hχ0:=hχ0) (hχ1:=hχ1) (hm:=hm) (hα:=hα) (hαhalf:=hαhalf) (hζ:=hζ)
  (p:=p) (Bcur:=Bcur) (Bword:=Bword)
local notation "AK"=>ActualGaussianMasterBound.linearK (ell:=D.ell) (M:=D.cap) (hell:=D.ell_pos) (D:=D)
  (hT:=hT) (hT1:=hT1) (hsmall:=hsmall) (N:=N) (ρ:=ρ) (χ:=χ) (ε:=ε) (tail:=tail) (ζ:=ζ)
  (hρ:=hρ) (hρhalf:=hρhalf) D.cap_nonneg ηmark
local notation "BM"=>ActualGaussianMasterBound.linearM (D:=D) (ρ:=ρ) (χ:=χ) (ε:=ε) (tail:=tail) (ζ:=ζ)
local notation "CE"=>ActualGaussianCompanionAttachment.energyConstant ρ (ell:=D.ell) (M:=D.cap)
local notation "Error" k:max n:max=>ActualGaussianCompanionAttachment.ordinaryEnergy
  (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ k) (κ:=κ) (hκ:=hκ) (haU:=Umeas) (haV:=Vmeas n)
  (hell:=D.ell_pos) (hbU:=D.residual_bounds) (hbV:=D.smooth_bounds n) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S k n)
  (P:=Smooth n) (haP:=Pbnd n) (D:=D) (n:=n) (Jbase:=cut k) (hL:=hΛ1 k) (hρ:=hρ) (N:=N)
local notation "Budget" k:max=>ActualGaussianCompanionAttachment.ordinaryBudget
  (D:=D) (hT:=hT) (hT1:=hT1) (hsmall:=hsmall) (κ:=κ) (M:=D.cap) (H:=H)
  (Λ:=Λ k) (ρ:=ρ) (N:=N) (Jbase:=cut k) Berror

include N ρ χ χref η ε tail ζ εref ηref hρ hρhalf hχ0 hχ1 hm hα hαhalf hζ p Bcur Bword Bref
  hκD hIJ₀ hIJ₁ hnull hJ hlocal hlocalI hFstop hHpos hH hsmallProfile hsmallL2 hcut hfreq hlow
  hχref hχref1 hεref hεrefhalf hηref hp hη hηmark hηmarkβ hηleaf hηleafβ hleafOrder hoLeaf0 hoLeaf1 hdepth
  hBI0 hBI1 hB16 hBDGpast hBDGnext hBDG4 hBDG8 hBDG1 hBDGcur hBDGword hBDGref hBDGerror hBDGleaf hBDGcov
  horder horderref htail hρeq hχeq hχrefeq hεrefeq hηrefeq hqh hqr hΛ1 in
/-- Uniform per-space actual inputs for a finite collection of original spaces.
No master, error-budget, or energy-relation premise is supplied. -/
theorem facts(k n:ℕ):
    let C:=max C0 CE;
    0<C ∧ (
      sqrt (Global k n)≤C*energyScale D.beta (Λ k)*sqrt (Neg k n ρ).toReal ∧
      ∀L:ℕ,(Error k n) L≤(ScalarApproximationDiscrepancy.scalarError D n)^2*(Budget k) L ∧
        ActualReferenceMasterClosure.Bound D.beta C (Λ k) (sqrt (Neg k n ρ).toReal) (sqrt (Global k n))
          (sqrt ((Error k n) L)+ActualTerminalReconstructionEnergy.error D n (cut k) L+HC*(Λ k)^(-(HQ 3/8)))
          (AK (Λ k)) (BM (Λ k)) 0 0):=by
  let C:=max C0 CE
  have hC0:0<C0:=ActualGaussianMasterBound.constant_pos (Ω:=Ω) (P:=Pzero) (D:=D) (hT:=hT) (hT1:=hT1) (hsmall:=hsmall)
    (κ:=κ) (ell:=D.ell) (M:=D.cap) (H:=H) (hell:=D.ell_pos) (hκP:=FloorPos 0) (ρ:=ρ) (hρ:=hρ) (hρhalf:=hρhalf)
    (N:=N) (Bnext:=Bnext) (χ:=χ) (η:=η) (ε:=ε) (tail:=tail) (ζ:=ζ)
    (hχ0:=hχ0) (hχ1:=hχ1) (hm:=hm) (hα:=hα) (hαhalf:=hαhalf) (hζ:=hζ)
    (p:=p) (Bcur:=Bcur) (Bword:=Bword) (Bref:=Bref) ηleaf leafOrder Bleaf B1 Bcov hqh
  have hC:0≤C:=(lt_of_lt_of_le hC0 (le_max_left _ _)).le
  refine ⟨lt_of_lt_of_le hC0 (le_max_left _ _),?_⟩
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
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ k) (κ:=κ) (hκ:=hκ) (haU:=Umeas) (haV:=Vmeas n) (hell:=D.ell_pos) (hbU:=D.residual_bounds) (hbV:=D.smooth_bounds n)
    (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S k n) (P:=Smooth n) (haP:=Pbnd n) (D:=D) (hT:=hT) (hT1:=hT1) (hsmall:=hsmall) (n:=n)
    (J:=J) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (hnull:=hnull) (hJ:=hJ) (hAs:=TotalBnd n) (N:=N) (Jbase:=cut k)
    (ρ:=ρ) (χ:=χ) (χref:=χref) (η:=η) (ε:=ε) (tail:=tail) (ζ:=ζ) (εref:=εref) (ηref:=ηref)
    (hρ:=hρ) (hχ0:=hχ0) (hχ1:=hχ1) (hm:=hm) (hα:=hα) (hαhalf:=hαhalf) (hζ:=hζ)
    (hχref:=hχref) (hχref1:=hχref1) (hεref:=hεref) (hεrefhalf:=hεrefhalf) (hηref:=hηref)
    (p:=p) (hp:=hp) (Bcur:=Bcur) (Bword:=Bword) (Bref:=Bref) (hκP:=FloorPos n) (hH:=hH) (hL:=hΛ1 k) (hρhalf:=hρhalf)
    (BI0:=BI0) (BI1:=BI1) (B16:=B16) (hBI0:=hBI0) (hBI1:=hBI1) (hB16:=hB16) (hJH:=hJH)
    (Bpast:=Bpast) (hBDGpast:=hBDGpast) (hlocalI:=hlocalI) (Bnext:=Bnext) (hBDGnext:=hBDGnext)
    (hFstop:=hFstop) (B4:=B4) (B8:=B8) (hBDG4:=hBDG4) (hBDG8:=hBDG8)
    (hβsmall:=D.beta_le) (hρeq:=hρeq) (hJP:=hJP) (hJF:=hJF) (hJC:=hJC) (hJS:=hJS) (hJG:=hJG)
    (CanonicalCompanionExpansion.total_eq D n hT hT1 hsmall hκD rfl) rfl hlocal hHpos (hsmallProfile n) (hsmallL2 n) B1 hBDG1 hBDGcur hBDGword hBDGref
    horder horderref htail hη hJbase (hfreq k) D.cap_nonneg ηmark hηmark hηmarkβ hAge hOld hqr hqh rfl rfl
    Berror hBDGerror hdepth ηleaf hηleaf hηleafβ leafOrder hleafOrder hoLeaf0 hoLeaf1 Bleaf Bcov hBDGleaf hBDGcov
    hχeq hχrefeq hεrefeq hηrefeq (hlow k)

  have hc:=ActualGaussianMasterBound.constant_congr (Ω:=Ω) (P:=Smooth n) (D:=D) (hT:=hT) (hT1:=hT1) (hsmall:=hsmall)
    (κ:=κ) (ell:=D.ell) (M:=D.cap) (H:=H) (hell:=D.ell_pos) (hκP:=FloorPos n) (ρ:=ρ) (hρ:=hρ) (hρhalf:=hρhalf)
    (N:=N) (Bnext:=Bnext) (χ:=χ) (η:=η) (ε:=ε) (tail:=tail) (ζ:=ζ)
    (hχ0:=hχ0) (hχ1:=hχ1) (hm:=hm) (hα:=hα) (hαhalf:=hαhalf) (hζ:=hζ)
    (p:=p) (Bcur:=Bcur) (Bword:=Bword) (Bref:=Bref) Pzero (FloorPos 0) rfl rfl rfl rfl ηleaf leafOrder Bleaf B1 Bcov
  rw [hc] at hpkg
  exact ⟨hpkg.2.2.1,fun L=>⟨(hpkg.2.2.2 L).2.1,(hpkg.2.2.2 L).2.2⟩⟩
end SHE.ActualGaussianCompanionUniform
