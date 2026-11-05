module
public import SHE.NativeConditionalThetaFields
public import SHE.MixedPastNativeOmitted
public import SHE.MixedPastLiteralFields
public import SHE.MixedPastNativeCovariance
public import SHE.NativeReserveRowEnvelope

public import SHE.MixedPastTwoFreshCovarianceInput
public import SHE.NativeResidualInputApplicability
public import SHE.MixedPastCovariancePointMoments
public import SHE.MixedPastProfileDerivative
public import SHE.ControlledThetaNativeCovariance
public import SHE.ActualCovarianceMarkFields
public import SHE.MixedPastCovarianceMass
public import SHE.ControlledThetaRelativeCovarianceMark
public import SHE.MixedPastLiteralPoint
public import SHE.ControlledThetaRelativeArrays
public import SHE.ControlledThetaWeightedFields
public import SHE.MixedPastDecayedWord
public import SHE.RelativeHistoryGeometry
public import SHE.ParentHeatFields
public import SHE.MixedPastActualMean
public import SHE.MixedPastJointData
public import SHE.MixedNativeJointHistory
public import SHE.ControlledJointMeanIdentity
public import SHE.CarrierStopBounds
public import SHE.CoveredControlledLaw
public import SHE.JointWordAnalytic
public import SHE.PastEventWeights
public import SHE.VaryingControlledGaussianFields
public import SHE.MixedNativePastWeightedMoments
public import SHE.MixedNativePastThetaMoments
public import SHE.NativePastHybridMoments
public import SHE.ControlledProfile
public import SHE.PastHybridIntegral
public import SHE.PastItoAlgebra
public import SHE.MixedNativePairObservation
public import SHE.NativePairScaledMartingale
public import SHE.NativePairLocalMartingale
public import SHE.NativePairExtendedMartingale

public import SHE.MixedPastNativeMarkThetaFields
public import SHE.ScalarFibreRMS
public import SHE.MixedPastNativeBaselineLeaf
@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastNativeThetaRMSFields
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastLiteralCovariance_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastLiteralCovariance_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastLiteralCovariance_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastLiteralCovariance_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastLiteralCovariance_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastLiteralCovariance_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

open PastItoInputs PastItoAlgebra PhysicalProfile


local instance mixedPastLiteralCovariance_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastLiteralCovariance_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {n : ℕ}



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open scoped BigOperators
local instance mixedPastLiteralCovariance_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : X×WordRecursion.State n=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v


attribute [local irreducible] MixedPastJointData.pastU MixedPastJointData.pastD

/-- The literal signed-profile absolute covariance score mass on the
original history, before selecting an output row or averaging theta. -/
def mass (k:ℕ)(θ:ℝ)(q:ℝ≥0)(h:History X k)(ω:Ω):ℝ:=
  let σ:=fun i=>stops Zero k h i-(v:ℝ)
  let target:=fun i=>targets Zero k h i-(v:ℝ)
  let lo:=fun j=>lower Zero k h j-(v:ℝ)
  let hi:=fun j=>upper Zero k h j-(v:ℝ)
  let B:=ControlledFixedReserve.covariance P Λ (U ω) (Dir ω)
    (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ (U ω) (Dir ω) lo hi))
    σ target (centers Zero k h) ((q:ℝ)-(v:ℝ)) θ
  ∫x,|ControlledProfile.derivative P Λ (U ω) (Dir ω) (x,θ)| *
    scoreVariance B (StoppedGaussianFeatures.stoppedRow σ target (centers Zero k h) x)
      ∂StoppedGaussianFeatures.historyMeasure ((q:ℝ)-(v:ℝ))

local notation "Mass"=>mass
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

theorem mass_measurable (hΛ:0≤Λ)
    (hsmall:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k:ℕ)(q:ℝ≥0)(h:History X k):
    Measurable (fun z:ℝ×Ω=>Mass k z.1 q h z.2):=by
  let σ:=fun i=>stops Zero k h i-(v:ℝ)
  let target:=fun i=>targets Zero k h i-(v:ℝ)
  let lo:=fun j=>lower Zero k h j-(v:ℝ)
  let hi:=fun j=>upper Zero k h j-(v:ℝ)
  have hU:=(MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hd:=(MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hB:=NativeConditionalThetaFields.residual_measurable P Λ ((q:ℝ)-(v:ℝ))
    (fun z:ℝ×Ω=>U z.2) (fun z:ℝ×Ω=>Dir z.2) (hU.comp measurable_snd) (hd.comp measurable_snd)
    Prod.fst measurable_fst σ target (centers Zero k h) lo hi
  have hrow:=(StoppedGaussianFeatures.stoppedRow_measurable σ target (centers Zero k h)).comp
    (measurable_snd:Measurable (Prod.snd:(ℝ×Ω)×StoppedGaussianFeatures.Domain→StoppedGaussianFeatures.Domain))
  have hscore:=scoreVariance_measurable.comp ((hB.comp measurable_fst).prodMk hrow)
  have he:=(ControlledProfile.random_derivative_measurable P hΛ U Dir hU hd hsmall).comp
    ((measurable_fst.snd.prodMk measurable_snd).prodMk measurable_fst.fst)
  have hh:=(((continuous_abs.measurable.comp he).mul hscore).stronglyMeasurable.integral_prod_right'
    (ν:=StoppedGaussianFeatures.historyMeasure ((q:ℝ)-(v:ℝ)))).measurable
  convert! hh using 1

/-- The genuine sample RMS is measurable before its theta integral. -/
theorem mass_rms_measurable (hΛ:0≤Λ)
    (hsmall:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k:ℕ)(q:ℝ≥0)(h:History X k):
    Measurable (fun θ:ℝ=>Real.sqrt (∫ω,|Mass k θ q h ω|^2 ∂μ)):=by
  have hm:=(mass_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hΛ hsmall k q h).comp measurable_swap
  exact ScalarFibreRMS.measurable μ _ hm

/-- Complete baseline leaf, with its correlated original profile input,
is jointly Borel before any theta/sample interchange. -/
theorem baseline_measurable (hΛ:0≤Λ)
    (hsmall:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k:ℕ)(q:ℝ≥0)(h:History X k)(E:WordRecursion.State (n+k))(j:Fin k):
    Measurable (fun z:ℝ×Ω=>MixedPastNativeBaselineLeaf.value
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k z.1 q h E j z.2):=by
  have he:=(MixedPastOmittedMarkFields.leaf_input_joint_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hΛ hsmall k j).comp
      (measurable_id.prodMk (measurable_const (a:=h)))
  have hg:=MixedPastNativeMarkThetaFields.omitted_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k q h E j
  have hh:=he.mul hg
  convert! hh using 1

end SHE.MixedPastNativeThetaRMSFields
