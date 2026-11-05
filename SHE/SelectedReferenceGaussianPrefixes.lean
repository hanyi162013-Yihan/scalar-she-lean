module
public import SHE.CommonReferenceGaussianFamily
public import SHE.HilbertENNFinitePrefixes
public import SHE.NativeFinitePrefixVersionTransfer
import all SHE.CommonReferenceGaussianFamily
public import SHE.MixedNativeReferenceGaussianTailFamily
public import SHE.FiniteNativeGaussianCutoff
public import SHE.FullReferenceClockIdentity
public import SHE.PastReferenceConstantUniform
public import SHE.MixedNativeHigherGaussianBand
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
namespace SHE.SelectedReferenceGaussianPrefixes
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

local notation "Actual"=>MixedNativeReferenceGaussianFamily.actual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP D n (fun _:HeatCircle=>(1:ℝ)) measurable_const (W:=1) zero_le_one (fun _=>by norm_num)
local notation "Literal"=>MixedNativeReferenceGaussianFamily.literal 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P D n (fun _:HeatCircle=>(1:ℝ)) measurable_const (W:=1) zero_le_one (fun _=>by norm_num)
  J hIJ₀ hIJ₁ hnull hJ hAs
local notation "Smooth"=>ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall
local notation "Rough"=>ControlledSmoothLimit.roughTotalParameters D hT hT1 hsmall
local notation "Amp"=>CanonicalGaussianRootBands.amplitude D 1
local notation "Global"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

local notation "Original"=>FullReferenceClockIdentity.original
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P J hIJ₀ hIJ₁ hnull hJ hAs
local notation "Bare"=>CanonicalGaussianBareRoot.test D n
local notation "BU"=>CanonicalGaussianBareRoot.uniform D n
local notation "BM"=>CanonicalGaussianBareRoot.measurable D n

include haP hIJ₀ hIJ₁ hnull hJ hAs in
theorem prefixes(hA:P.coefficient=(fun z=>κ+aV z))
    (hlocal:StandardTerminalPastLocality J)(hL:1≤Λ){ρ:ℝ}(hρ:0<ρ)(hρhalf:ρ<1/2)
    (hHpos:0<H)(hH:(H:ℝ)≤1)
    (hsmallPoint:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k:ℕ)(hP:P=Smooth n)(χ:ℝ)(hχ:0<χ)(hχ1:χ<1)
    (p:ℕ)(hp:0<p)(horder:1≤(p:ℝ)*(1-χ))
    (Bpast Babs B0:ℝ≥0)(hBDGpast:StandardTerminalBDGPower 1 J Bpast)
    (hBDGabs:StandardTerminalBDGPower (k+2) J Babs)
    (hBDG:StandardTerminalBDGPower ((2*p)*(k+2)) J B0)
    (ε:ℝ)(hε:0≤ε)(hεhalf:ε<1/2)(η:ℝ)(hη:0<η)
    (N Jbase:ℕ)(hk:0<k)(hkN:k≤N)
    (hJbase:FiniteNativeGaussianCutoff.index D hT hT1 hsmall H hHpos N≤Jbase)
    (F:ℕ→ℝ≥0×Ω→CircleL2)(hF:∀j,Measurable (F j))
    (hFa:∀j,∀ᵐt∂timeMeasure H,(fun ω=>F j (t,ω))=ᵐ[μ]
      (fun ω=>Original (Bare (j+Jbase+1)) (BU (j+Jbase+1)) (BM (j+Jbase+1))
        (RemainderBandSpans.span D.beta (j+Jbase+1)) hL hρ.le k (t,ω)))
    (hq:∀i:Fin 3,0<MixedNativeReferenceGaussianFamily.degrees D.beta ρ ε η k i):
    let q:=MixedNativeReferenceGaussianFamily.degrees D.beta ρ ε η k
    let K:=MixedNativeReferenceGaussianFamily.coefficients Rough κ M Λ Global (H:ℝ) (Amp k) k p Babs B0 ρ χ ε η
    let Y:=fun j=>Actual hL hρ.le k (j+Jbase+1)
    ∀L:ℕ,Integrable (fun z=>‖∑j∈Finset.range L,F j z‖^2) (energyMeasure μ H) ∧
      sqrt (∫z,‖∑j∈Finset.range L,F j z‖^2 ∂energyMeasure μ H)≤
        ∑i:Fin 3,sqrt (K i).toReal*StateBands.geometricConstant (q i/2)*
          ((2:ℝ)^(Jbase+1))^(-(q i/2)):=by
  intro q K Y
  obtain ⟨hY,hYa,hi,hK,hb⟩:=CommonReferenceGaussianFamily.family
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP D hT hT1 hsmall n
    J hIJ₀ hIJ₁ hnull hJ hAs hA hlocal hL hρ hρhalf hHpos hH hsmallPoint hsmallL2
    k hP χ hχ hχ1 p hp horder Bpast Babs B0 hBDGpast hBDGabs hBDG ε hε hεhalf η hη N Jbase hk hkN hJbase
  have he:=NativeFinitePrefixVersionTransfer.of_sections μ H F Y
    (fun j z=>Original (Bare (j+Jbase+1)) (BU (j+Jbase+1)) (BM (j+Jbase+1))
      (RemainderBandSpans.span D.beta (j+Jbase+1)) hL hρ.le k z) hF hY hFa hYa
  apply NativeFinitePrefixVersionTransfer.prefixes μ H F Y he
  exact HilbertENNFinitePrefixes.rms (energyMeasure μ H) Y hY hi (Jbase+1) q K hq hK
    (fun j=>by simpa only [Y,K,q,Nat.add_assoc] using hb j)
end SHE.SelectedReferenceGaussianPrefixes
