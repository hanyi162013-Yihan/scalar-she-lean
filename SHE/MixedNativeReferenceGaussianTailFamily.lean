module
public import SHE.MixedNativeReferenceGaussianFamily
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
namespace SHE.MixedNativeReferenceGaussianTailFamily
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
variable (n:ℕ)(ψ:HeatCircle→ℝ)(hψm:Measurable ψ)
variable {W:ℝ}(hW:0≤W)(hψ:∀x,|ψ x|≤W)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)(hJ:StandardFiniteIto.Universal 𝓕 μ H J)
variable (hAs:BoundedSmooth (fun z=>κ+aV z))

local notation "Actual"=>MixedNativeReferenceGaussianFamily.actual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP D n ψ hψm hW hψ
local notation "Literal"=>MixedNativeReferenceGaussianFamily.literal 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P D n ψ hψm hW hψ
  J hIJ₀ hIJ₁ hnull hJ hAs
local notation "Smooth"=>ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall
local notation "Rough"=>ControlledSmoothLimit.roughTotalParameters D hT hT1 hsmall
local notation "Amp"=>CanonicalGaussianRootBands.amplitude D W
local notation "Global"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

include haP hIJ₀ hIJ₁ hnull hJ hAs in
theorem family_from(hA:P.coefficient=(fun z=>κ+aV z))
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
    (J0:ℕ)(hJ0:NativeGaussianWindowCutoff.index D hT hT1 hsmall H hHpos k≤J0):
    let q:=MixedNativeReferenceGaussianFamily.degrees D.beta ρ ε η k
    let K:=MixedNativeReferenceGaussianFamily.coefficients Rough κ M Λ Global (H:ℝ) (Amp k) k p Babs B0 ρ χ ε η
    let Y:=fun j=>Actual hL hρ.le k (j+J0)
    (∀j,Measurable (Y j)) ∧
    (∀j,∀ᵐt∂timeMeasure H,∀ᵐω∂μ,Y j (t,ω)=Literal hL hρ.le k (j+J0) (t,ω)) ∧
    (∀j,Integrable (fun z=>‖Y j z‖^2) (energyMeasure μ H)) ∧
    (∀i:Fin 3,K i≠∞) ∧
    ∀j,(∫⁻z,ENNReal.ofReal (‖Y j z‖^2) ∂energyMeasure μ H)≤
      ∑i,K i*ENNReal.ofReal (((2:ℝ)^(j+J0))^(-q i)) :=by
  intro q K Y
  obtain ⟨hY,hYa,hi,hK,hb⟩:=MixedNativeReferenceGaussianFamily.family
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP D hT hT1 hsmall n ψ hψm hW hψ
    J hIJ₀ hIJ₁ hnull hJ hAs hA hlocal hL hρ hρhalf hHpos hH hsmallPoint hsmallL2
    k hP χ hχ hχ1 p hp horder Bpast Babs B0 hBDGpast hBDGabs hBDG ε hε hεhalf η hη
  let base:=NativeGaussianWindowCutoff.index D hT hT1 hsmall H hHpos k
  let shift:=J0-base
  have hs:shift+base=J0:=Nat.sub_add_cancel hJ0
  have he(j:ℕ):j+shift+NativeGaussianWindowCutoff.index D hT hT1 hsmall H hHpos k=j+J0:=by omega
  refine ⟨?_,?_,?_,hK,?_⟩
  · intro j
    simpa only [Y,he] using hY (j+shift)
  · intro j
    simpa only [Y,he] using hYa (j+shift)
  · intro j
    simpa only [Y,he] using hi (j+shift)
  · intro j
    simpa only [Y,he] using hb (j+shift)

end SHE.MixedNativeReferenceGaussianTailFamily
