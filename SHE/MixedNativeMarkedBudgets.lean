module

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
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000

namespace SHE.MixedNativeMarkedBudgets
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedNativeMarkedBudgets_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeMarkedBudgets_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeMarkedBudgets_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeMarkedBudgets_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeMarkedBudgets_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeMarkedBudgets_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedNativeMarkedBudgets_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedNativeMarkedBudgets_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {n : ℕ}



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance mixedNativeMarkedBudgets_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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

/-- Actual random-past native endpoint of the canonical finite-depth
reference word, on the original active history/current-time window. -/
def endpoint (k : ℕ) (θ : ℝ) (q : ℝ≥0) (ω : Ω) (h : History X k) : ℝ:=
  ControlledFamilyFrontFields.activeValue P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
    (U ω,Dir ω) k h q (CU q ω) (CD q ω) θ

def covariance (k : ℕ) (θ : ℝ) (q : ℝ≥0) (ω : Ω) (h : History X k) : ℝ:=
  ControlledFamilyLegFubini.covariance P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
    (U ω,Dir ω) k h q (CU q ω) (CD q ω) θ

def mean (k : ℕ) (θ : ℝ) (q : ℝ≥0) (ω : Ω) (h : History X k) : ℝ:=
  ControlledFamilyLegFubini.mean P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
    (U ω,Dir ω) k h q (CU q ω) (CD q ω) θ

def baseline (k : ℕ) (θ : ℝ) (q : ℝ≥0) (ω : Ω) (h : History X k) : ℝ:=
  ControlledFamilyLegFubini.baseline P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
    (U ω,Dir ω) k h q (CU q ω) (CD q ω) θ

local notation "Endpoint"=>endpoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "C"=>covariance 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "M"=>mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "B"=>baseline 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm

/-- Exact actual mixed-native finite-history transfer. All random-past
and current-state Borel conditions are proved from the constructed
pair; the only displayed integration inputs are the three literal
absolute L¹ section budgets with integrable theta envelopes. -/
theorem expected_transfer (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hroot : ∀ x i,(Z.observations x i).stop=(b:ℝ))
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) (q : ℝ≥0)
    (Ec Em Eb : ℝ→ℝ)
    (hEc : IntervalIntegrable Ec volume 0 1) (hEm : IntervalIntegrable Em volume 0 1)
    (hEb : IntervalIntegrable Eb volume 0 1)
    (hC : ∀ᵐ θ ∂volume.restrict (Ioc (0:ℝ) 1),
      Integrable (fun z : Ω×History X k=>C k θ q z.1 z.2)
        (μ.prod (historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) ρ k)) ∧
      (∫ z : Ω×History X k,|C k θ q z.1 z.2|
        ∂μ.prod (historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) ρ k))≤Ec θ)
    (hM : ∀ᵐ θ ∂volume.restrict (Ioc (0:ℝ) 1),
      Integrable (fun z : Ω×History X k=>M k θ q z.1 z.2)
        (μ.prod (historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) ρ k)) ∧
      (∫ z : Ω×History X k,|M k θ q z.1 z.2|
        ∂μ.prod (historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) ρ k))≤Em θ)
    (hB : ∀ᵐ θ ∂volume.restrict (Ioc (0:ℝ) 1),
      Integrable (fun z : Ω×History X k=>B k θ q z.1 z.2)
        (μ.prod (historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) ρ k)) ∧
      (∫ z : Ω×History X k,|B k θ q z.1 z.2|
        ∂μ.prod (historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) ρ k))≤Eb θ) :
    IntervalIntegrable (fun θ=>∫ ω,(∫ h,C k θ q ω h+M k θ q ω h+B k θ q ω h
      ∂historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) ρ k) ∂μ) volume 0 1 ∧
    (∫ θ in (0:ℝ)..1,∫ ω,(∫ h,C k θ q ω h+M k θ q ω h+B k θ q ω h
      ∂historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) ρ k) ∂μ)=
      (∫ ω,(∫ h,Endpoint k 1 q ω h ∂historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) ρ k) ∂μ)-
      (∫ ω,(∫ h,Endpoint k 0 q ω h ∂historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) ρ k) ∂μ) := by
  have hUv:=(MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hDv:=(MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hUq:=(MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q).mono (𝓕.le q) le_rfl
  have hDq:=(MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q).mono (𝓕.le q) le_rfl
  have he:=ControlledFamilyBudgetTransfer.expected_transfer_of_leg_budgets
    P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm hΛ hsmall hroot hspan μ ρ k
    (fun ω=>(U ω,Dir ω)) (hUv.prodMk hDv) (fun _=>(q:ℝ)) measurable_const
    (fun ω=>CU q ω) (fun ω=>CD q ω) hUq hDq
    Ec Em Eb hEc hEm hEb hC hM hB
  simpa only [ControlledFamilyLegFubini.active_mark_eq,covariance,mean,baseline,endpoint] using he

end SHE.MixedNativeMarkedBudgets
