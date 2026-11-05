module

public import SHE.MixedNativeTreeEndpoints
public import SHE.HistoryPastWindow
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

namespace SHE.MixedNativeTreeAverages
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedNativeTreeAverages_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeTreeAverages_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeTreeAverages_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeTreeAverages_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeTreeAverages_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeTreeAverages_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedNativeTreeAverages_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedNativeTreeAverages_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {n : ℕ}



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance mixedNativeTreeAverages_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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

local notation "R₀"=>referenceData P P.coefficient haP Λ 0 v b hvb (0,0)

/-- The actual joint reference endpoint in the finite mixed tree. -/
def jointReference (k : ℕ) (ω : Ω) (h : History X k) : ℝ:=
  JointUncutWordEvaluation.reference (Base (1,(U ω,Dir ω))) Λ
    (dU).physicalState (dV).physicalState (dU).physicalField (dV).physicalField k h ω

/-- The ordinary uncontrolled reference at the actual first past
state, with its theta-zero canonical profile and recursive test. -/
def uncontrolledReference (k : ℕ) (ω : Ω) (h : History X k) : ℝ:=
  UncutWordEvaluation.reference (Base (0,(U ω,Dir ω))) (U ω) k h

local notation "Joint"=>jointReference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Ordinary"=>uncontrolledReference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm

/-- One original-history event identifies BOTH actual endpoints with
the appropriate tree references for EVERY original sample. -/
theorem endpoints_eq_references_ae
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(b:ℝ))
    (hvb' : v<b) (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure R₀ ρ k,∀ ω : Ω,
      Endpoint k 1 v ω h=Joint k ω h ∧ Endpoint k 0 v ω h=Ordinary k ω h := by
  have hroot : ∀ x,(v:ℝ)<(Zero).terminal x:=fun _=>by exact_mod_cast hvb'
  filter_upwards [HistoryPastWindow.carrier_after_past_ae Zero hroot ρ k] with h hh
  intro ω
  exact ⟨MixedNativeTreeEndpoints.endpoint_one_eq_joint_reference
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
      hages hrootStop k h ω hh,
    MixedNativeTreeEndpoints.endpoint_zero_eq_uncontrolled_reference
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm k h ω hh⟩

/-- The native endpoint is integrable on the original sample/history
product; bounded smooth-root recursive mass supplies this directly. -/
theorem endpoint_integrable (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) (θ : ℝ) :
    Integrable (fun z : Ω×History X k=>Endpoint k θ v z.1 z.2) (μ.prod (historyMeasure R₀ ρ k)) := by
  have hU:=(MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hD:=(MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  exact ControlledFamilyExpectedTransfer.endpoint_product_integrable
    P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm μ ρ k
    (fun ω=>(U ω,Dir ω)) (hU.prodMk hD) (fun _=>(v:ℝ)) measurable_const
    (fun ω=>CU v ω) (fun ω=>CD v ω) hU hD θ

/-- The literal two reference fields are integrable on the original
product measure, even though the reference input depends on the same
sample. Equality holds on a common event before any averaging. -/
theorem references_integrable
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(b:ℝ))
    (hvb' : v<b) (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    Integrable (fun z : Ω×History X k=>Joint k z.1 z.2) (μ.prod (historyMeasure R₀ ρ k)) ∧
    Integrable (fun z : Ω×History X k=>Ordinary k z.1 z.2) (μ.prod (historyMeasure R₀ ρ k)) := by
  have he:=endpoints_eq_references_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm hages hrootStop hvb' ρ k
  have hep : ∀ᵐ z : Ω×History X k ∂μ.prod (historyMeasure R₀ ρ k),
      Endpoint k 1 v z.1 z.2=Joint k z.1 z.2 ∧ Endpoint k 0 v z.1 z.2=Ordinary k z.1 z.2 :=
    (Measure.quasiMeasurePreserving_snd.ae he).mono (fun z hz=>hz z.1)
  exact ⟨(endpoint_integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm ρ k 1).congr (hep.mono (fun _ h=>h.1)),
    (endpoint_integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm ρ k 0).congr (hep.mono (fun _ h=>h.2))⟩

/-- Exact expected endpoint difference in terms of the two ACTUAL
finite-tree reference terms. The theta-zero term is the uncontrolled
reference, not the full-D joint reference with its profile set to zero. -/
theorem expected_endpoint_difference
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(b:ℝ))
    (hvb' : v<b) (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    (∫ ω,(∫ h,Endpoint k 1 v ω h ∂historyMeasure R₀ ρ k) ∂μ)-
      (∫ ω,(∫ h,Endpoint k 0 v ω h ∂historyMeasure R₀ ρ k) ∂μ)=
    (∫ ω,(∫ h,Joint k ω h ∂historyMeasure R₀ ρ k) ∂μ)-
      (∫ ω,(∫ h,Ordinary k ω h ∂historyMeasure R₀ ρ k) ∂μ) := by
  have he:=endpoints_eq_references_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm hages hrootStop hvb' ρ k
  congr 1
  · apply integral_congr_ae
    exact ae_of_all _ (fun ω=>integral_congr_ae (he.mono (fun h hh=>(hh ω).1)))
  · apply integral_congr_ae
    exact ae_of_all _ (fun ω=>integral_congr_ae (he.mono (fun h hh=>(hh ω).2)))

end SHE.MixedNativeTreeAverages
