module

public import SHE.ControlledFamilyBaselineFieldsBorel
public import SHE.MixedNativeMarkedBudgets
public import SHE.MixedPastBaselineFTCIdentity
public import SHE.ControlledFamilyBudgetTransfer
public import SHE.ControlledFamilyBaselineLeg
public import SHE.ControlledFamilyLegFubini
public import SHE.MixedPastLiteralMean
public import SHE.MixedPastLiteralOmitted
public import SHE.ControlledThetaOmittedFields
public import SHE.ControlledFamilyProfileMarkFields
public import SHE.MixedPastLiteralFields
public import SHE.JointInterpolationFields
public import SHE.WeightedRowTimeShift
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

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedNativeBaselineJointFields
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedNativeBaselineJointFields_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeBaselineJointFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeBaselineJointFields_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeBaselineJointFields_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeBaselineJointFields_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeBaselineJointFields_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

open PastItoInputs PastItoAlgebra PhysicalProfile


local instance mixedNativeBaselineJointFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedNativeBaselineJointFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {n : ℕ}



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance mixedNativeBaselineJointFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedNativeBaselineJointFields_circleSecondCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology

variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : X×WordRecursion.State n=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v


local notation "Mean"=>MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P haP v b hvb Z htarget hstop F hF hFm
local notation "Input"=>MixedPastOmittedMarkFields.leafInput 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P haP v b hvb Z htarget hstop F hF hFm
local notation "Leaf"=>MixedPastOmittedMarkFields.leafMark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P haP v b hvb Z htarget hstop F hF hFm
local notation "LP"=>ControlledFamilyThreeLeg.leafPoint P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm

local notation "CU"=>(fun (q:ℝ≥0) (ω:Ω)=>embed (S.first q ω))
local notation "CD"=>(fun (q:ℝ≥0) (ω:Ω)=>embed (S.second q ω-S.first q ω))

local notation "Leg"=>MixedNativeMarkedBudgets.baseline 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P haP v b hvb Z htarget hstop F hF hFm
local notation "dU"=>MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV"=>MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "R₀"=>referenceData P P.coefficient haP Λ 0 v b hvb (0,0)

/-- The literal actual baseline leg is jointly Borel in theta, real
current time, original sample and the entire physical history. Negative
real times are sent to zero by the actual NNReal clock. -/
theorem baseline_joint_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k : ℕ) :
    Measurable (fun z : (ℝ×ℝ)×(Ω×History X k)=>Leg k z.1.1 z.1.2.toNNReal z.2.1 z.2.2) := by
  have hUv:=(MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hDv:=(MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hUm : Measurable (fun z : (ℝ×ℝ)×(Ω×History X k)=>embed (S.first z.1.2.toNNReal z.2.1)) :=
    (dU).physicalState_measurable.comp (measurable_snd.fst.prodMk measurable_fst.snd)
  have hVm : Measurable (fun z : (ℝ×ℝ)×(Ω×History X k)=>embed (S.second z.1.2.toNNReal z.2.1)) :=
    (dV).physicalState_measurable.comp (measurable_snd.fst.prodMk measurable_fst.snd)
  have hDm : Measurable (fun z : (ℝ×ℝ)×(Ω×History X k)=>
      embed (S.second z.1.2.toNNReal z.2.1-S.first z.1.2.toNNReal z.2.1)) := by
    convert hVm.sub hUm using 1
    funext z
    exact map_sub embed _ _
  have hq : Measurable (fun z : (ℝ×ℝ)×(Ω×History X k)=>(z.1.2.toNNReal:ℝ)):=
    measurable_subtype_coe.comp (measurable_real_toNNReal.comp measurable_fst.snd)
  have hh := ControlledFamilyBaselineFieldsBorel.baseline_variable_measurable
    P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm hΛ hsmall (W := (ℝ×ℝ)×(Ω×History X k)) k
    (fun z : (ℝ×ℝ)×(Ω×History X k)=>(U z.2.1,Dir z.2.1)) ((hUv.comp measurable_snd.fst).prodMk (hDv.comp measurable_snd.fst))
    (fun z=>z.2.2) measurable_snd.snd (fun z=>(z.1.2.toNNReal:ℝ)) hq
    (fun z=>embed (S.first z.1.2.toNNReal z.2.1))
    (fun z=>embed (S.second z.1.2.toNNReal z.2.1-S.first z.1.2.toNNReal z.2.1))
    hUm hDm (fun z=>z.1.1) measurable_fst.fst
  simpa only [MixedNativeMarkedBudgets.baseline] using hh

/-- The genuine original-history average is jointly Borel in theta,
real current time and sample; no parameter-dependent exceptional set
is substituted into this integral. -/
theorem history_average_joint_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    Measurable (fun z : (ℝ×ℝ)×Ω=>∫ h,Leg k z.1.1 z.1.2.toNNReal z.2 h ∂historyMeasure R₀ ρ k) := by
  have hh:=(baseline_joint_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm hΛ hsmall k).comp
      (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  exact hh.stronglyMeasurable.integral_prod_right'.measurable

end SHE.MixedNativeBaselineJointFields
