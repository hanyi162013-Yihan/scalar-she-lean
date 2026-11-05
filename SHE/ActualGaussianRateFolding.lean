module
public import SHE.ActualGaussianFiniteRMS
public import SHE.NativeHigherMasterFiniteCoefficient
public import SHE.NativeReferenceMasterFiniteCoefficient
import all SHE.ActualGaussianFiniteRMS
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
namespace SHE.ActualGaussianRateFolding
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

variable (hρhalf:ρ<1/2)
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

def higherData(k:ℕ):(Fin 4→ℝ≥0∞)×(Fin 5→ℝ):=

  let d:=k+1
  let Cf:=NativeUniversalConstants.rowConstant (1+d)
  let Cdim:=NativeUniversalConstants.currentConstant.{0} (1+d) (by omega)
  let C:=MixedPastNativeQuarterRMS.coefficient κ (M:=M) Pzero d Cf ρ
  let Ccur:=sqrt (8*C*MixedPastNativeEnergyNormalization.currentCoefficient κ (M:=M) Pzero d p χ Cdim (Bcur k))
  let Cpast:=sqrt (2*C*MixedPastNativeEnergyNormalization.pastCoefficient κ (M:=M) Pzero d (Bword k))
  let Jt:=MixedPastSignedEndpointMoments.traceConstant (Ω:=Ω) (M:=M) hell ρ hρ hρhalf
  let Cmom:=MixedPastWordMoments.momentConstant Pzero d d p
    ((d:ℝ)*(NativeHybridMoments.momentConstant (p*(d+2)) (Bcur k) κ M)^(Pzero).exponent)
  let Cgood:=PastSignedEndpointTime.goodCoefficient Pzero d Jt ρ η
  let Cbad:=PastSignedEndpointTime.badCoefficient Pzero d M Cmom
  let A:=CanonicalGaussianRootBands.amplitude D 1 d
  let Cc:=NativeCanonicalFrequency.currentCoefficient D hT hT1 hsmall scoreFloor Cs d (by omega) ρ χ hρ hχ0 hχ1 hm ζ hζ
  let Ci:=NativeCanonicalFrequency.initialCoefficient D hT hT1 hsmall scoreFloor Cs d (by omega) ρ χ hρ hχ0 hχ1 hm ζ hζ
  let Cp:=NativeCanonicalFrequency.pastCoefficient D hT hT1 hsmall scoreFloor Cs d (by omega) ρ χ hρ hχ0 hχ1 hm ζ hζ
  let Cg:=NativeCanonicalFrequency.goodCoefficient D hT hT1 hsmall scoreFloor Cs d (by omega) ρ η ε tail ζ hα hαhalf hζ
  let Cb:=NativeCanonicalFrequency.badCoefficient D hT hT1 hsmall scoreFloor Cs d (by omega) ρ η ε tail ζ hα hαhalf hζ
  let q:=NativeFullRateCap.degree (NativeBandFrequencyRates.currentDegree D.beta ρ χ ζ)
    (NativeBandFrequencyRates.pastDegree D.beta ζ) (SignedNativeBandFrequency.goodDegree D.beta ε ζ)
    (SignedNativeBandFrequency.badDegree D.beta tail ζ)
  (![ENNReal.ofReal (8*A^2*Ccur^2),ENNReal.ofReal (8*A^2*Cpast^2),
    ENNReal.ofReal (4*A^2*Cgood^2),ENNReal.ofReal (4*A^2*Cbad^2)],![Cc,Ci,Cp,Cg,Cb])
local notation "Data"=>higherData (Ω:=Ω) (κ:=κ) (M:=M) (hell:=hell) (D:=D) (hT:=hT) (hT1:=hT1) (hsmall:=hsmall)
  (ρ:=ρ) (χ:=χ) (η:=η) (ε:=ε) (tail:=tail) (ζ:=ζ) (hρ:=hρ) (hρhalf:=hρhalf)
  (hχ0:=hχ0) (hχ1:=hχ1) (hm:=hm) (hα:=hα) (hαhalf:=hαhalf) (hζ:=hζ)
  (p:=p) (Bcur:=Bcur) (Bword:=Bword)

def higherConstant:ℝ:=NativeHigherMasterFiniteCoefficient.constant N
  (fun k=>(Data k).1 0) (fun k=>(Data k).1 1) (fun k=>(Data k).1 2) (fun k=>(Data k).1 3)
  (fun k=>(Data k).2 0) (fun k=>(Data k).2 1) (fun k=>(Data k).2 2)
  (fun k=>(Data k).2 3) (fun k=>(Data k).2 4)
  (NativeFullRateCap.degree (NativeBandFrequencyRates.currentDegree D.beta ρ χ ζ)
    (NativeBandFrequencyRates.pastDegree D.beta ζ) (SignedNativeBandFrequency.goodDegree D.beta ε ζ)
    (SignedNativeBandFrequency.badDegree D.beta tail ζ))
local notation "HC"=>higherConstant (Ω:=Ω) (κ:=κ) (M:=M) (hell:=hell) (D:=D) (hT:=hT) (hT1:=hT1) (hsmall:=hsmall)
  (N:=N) (ρ:=ρ) (χ:=χ) (η:=η) (ε:=ε) (tail:=tail) (ζ:=ζ) (hρ:=hρ) (hρhalf:=hρhalf)
  (hχ0:=hχ0) (hχ1:=hχ1) (hm:=hm) (hα:=hα) (hαhalf:=hαhalf) (hζ:=hζ)
  (p:=p) (Bcur:=Bcur) (Bword:=Bword)

/-- Exact actual higher coefficients fold into the two linear slots,
zero-damping native sublinear row, and the strict bad error tail. -/
theorem higher (hΛ:1≤Λ)(hH:(H:ℝ)≤1)
    (hfreq:Λ^(1/4:ℝ)≤(2:ℝ)^(Jbase+1))
    (hq:∀i:Fin 4,0<(NativeFullRateCap.degree (NativeBandFrequencyRates.currentDegree D.beta ρ χ ζ)
    (NativeBandFrequencyRates.pastDegree D.beta ζ) (SignedNativeBandFrequency.goodDegree D.beta ε ζ)
    (SignedNativeBandFrequency.badDegree D.beta tail ζ)) i):
    (∑k:Fin N,HCap k)≤
      let q:=(NativeFullRateCap.degree (NativeBandFrequencyRates.currentDegree D.beta ρ χ ζ)
        (NativeBandFrequencyRates.pastDegree D.beta ζ) (SignedNativeBandFrequency.goodDegree D.beta ε ζ)
        (SignedNativeBandFrequency.badDegree D.beta tail ζ))
      HC*(NativeHigherMasterFiniteCoefficient.signedLinear q Λ*sqrt (Neg ρ).toReal+
        NativeHigherMasterFiniteCoefficient.pastLinear q Λ*sqrt Global+(sqrt Global)^χ+Λ^(-(q 3/8))):=by
  have hg:0≤Global:=integral_nonneg (fun _=>sq_nonneg _)
  have he:(sqrt Global)^2=Global:=sq_sqrt hg
  have ht:=NativeHigherMasterFiniteCoefficient.cap N
    (fun k=>(Data k).1 0) (fun k=>(Data k).1 1) (fun k=>(Data k).1 2) (fun k=>(Data k).1 3)
    (fun k=>(Data k).2 0) (fun k=>(Data k).2 1) (fun k=>(Data k).2 2)
    (fun k=>(Data k).2 3) (fun k=>(Data k).2 4)
    (NativeFullRateCap.degree (NativeBandFrequencyRates.currentDegree D.beta ρ χ ζ)
    (NativeBandFrequencyRates.pastDegree D.beta ζ) (SignedNativeBandFrequency.goodDegree D.beta ε ζ)
    (SignedNativeBandFrequency.badDegree D.beta tail ζ)) hq (Neg ρ) hΛ hfreq (sqrt_nonneg Global) H.2 hH hχ1.le
  convert ht using 1 <;> simp only [higherConstant,higherData,ActualGaussianFiniteRMS.higherCap,he] <;> rfl

end SHE.ActualGaussianRateFolding
