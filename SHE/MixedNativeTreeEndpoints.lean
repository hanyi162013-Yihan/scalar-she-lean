module

public import SHE.MixedNativeMarkedBudgets
public import SHE.ControlledFamilyReferenceAtPast
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

namespace SHE.MixedNativeTreeEndpoints
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedNativeTreeEndpoints_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeTreeEndpoints_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeTreeEndpoints_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeTreeEndpoints_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeTreeEndpoints_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeTreeEndpoints_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedNativeTreeEndpoints_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedNativeTreeEndpoints_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {n : ℕ}



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance mixedNativeTreeEndpoints_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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

local notation "Endpoint"=>MixedNativeMarkedBudgets.endpoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "dU"=>MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV"=>MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S

omit [IsProbabilityMeasure μ] in
/-- The theta-zero endpoint is the ORDINARY uncontrolled Gaussian
reference at the actual first past state, with its own theta-zero
profile and recursive test. It is not the full joint state at theta zero. -/
theorem endpoint_zero_eq_uncontrolled_reference
    (k : ℕ) (h : History X k) (ω : Ω)
    (hactive : (v:ℝ)<(carrier Zero k).terminal h) :
    Endpoint k 0 v ω h=UncutWordEvaluation.reference (Base (0,(U ω,Dir ω))) (U ω) k h := by
  unfold MixedNativeMarkedBudgets.endpoint ControlledFamilyFrontFields.activeValue
  rw [ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient haP Λ v b hvb
    Z htarget hstop F hF hFm (0,(U ω,Dir ω)) (0,(0,0)) k h,ite_eq_left ⟨le_rfl,hactive⟩]
  exact ControlledFamilyReferenceAtPast.value_zero_at_past_eq_reference
    P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm (U ω,Dir ω) k h (CU v ω) (CD v ω)

/-- The theta-one endpoint is the literal joint reference in the
actual mixed finite expansion. Original stops are retained, and no
Gaussian law is asserted for the original current states. -/
theorem endpoint_one_eq_joint_reference
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(b:ℝ))
    (k : ℕ) (h : History X k) (ω : Ω)
    (hactive : (v:ℝ)<(carrier Zero k).terminal h) :
    Endpoint k 1 v ω h=JointUncutWordEvaluation.reference (Base (1,(U ω,Dir ω))) Λ
      (dU).physicalState (dV).physicalState (dU).physicalField (dV).physicalField k h ω := by
  unfold MixedNativeMarkedBudgets.endpoint ControlledFamilyFrontFields.activeValue
  rw [ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient haP Λ v b hvb
    Z htarget hstop F hF hFm (0,(U ω,Dir ω)) (0,(0,0)) k h,ite_eq_left ⟨le_rfl,hactive⟩,
    ControlledFamilyReferenceAtPast.value_at_past_eq_node_average P P.coefficient haP Λ v b hvb
      Z htarget hstop F hF hFm]
  have hm:=MixedPastBaselineFTCIdentity.mean_eq_meanField
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
    hages hrootStop k h 1 v hactive ω
  have hs:=MixedPastLiteralMean.meanField_one_eq_state
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
    hages hrootStop k h v hactive ω
  have hstate : JointWordAnalytic.state (carrier Zero k) Λ (dU).physicalState (dV).physicalState
      (dU).physicalField (dV).physicalField h ω v=
      JointWordAnalytic.state (carrier (Base (1,(U ω,Dir ω))) k) Λ
        (dU).physicalState (dV).physicalState (dU).physicalField (dV).physicalField h ω v := by
    unfold JointWordAnalytic.state
    rw [ControlledReferenceThetaGeometry.carrier_observations_eq P P.coefficient haP Λ v b hvb
      Z htarget hstop F hF hFm (1,(U ω,Dir ω)) (0,(0,0)) k h]
  have hmean:=hm.trans (hs.trans hstate)
  unfold JointUncutWordEvaluation.reference
  rw [hmean]
  rfl

end SHE.MixedNativeTreeEndpoints
