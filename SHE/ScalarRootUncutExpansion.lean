module

public import SHE.ScalarRootFiniteExpansion
public import SHE.JointUncutEvaluationLimit
public import SHE.JointRecursiveCutoffCorrection
public import SHE.MixedJointUncutMark
public import SHE.JointZeroHeatCycle
public import SHE.JointHeatLeafLimit
public import SHE.JointRecursiveReferenceLimit
public import SHE.JointRecursiveRemainderConvergence
public import SHE.FiniteWordExpectation
public import SHE.MixedJointIntegratedLevel
public import SHE.JointRecursiveHessian
public import SHE.NativeRowTargetContinuity
public import SHE.MixedNativeJointHistory
public import SHE.JointInsertionIntegrability
public import SHE.JointWordDefect

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
noncomputable section

namespace SHE.ScalarRootUncutExpansion
open MeasureTheory Set PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation CutoffWordLevel
open GaussianTaylorAverage JointWordAnalytic
open scoped ENNReal NNReal
local instance scalarRootUncutExpansionInstance1 : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance scalarRootUncutExpansionInstance2 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance scalarRootUncutExpansionInstance3 : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance scalarRootUncutExpansionInstance4 : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance scalarRootUncutExpansionInstance5 : MeasurableSpace CircleL2 := borel _
local instance scalarRootUncutExpansionInstance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance scalarRootUncutExpansionInstance7 : MeasurableSpace RealL2 := borel _
local instance scalarRootUncutExpansionInstance8 : BorelSpace RealL2 := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {R : ReferenceData} (L : Level R HeatCircle 1)
local notation "dU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U" => (dU).physicalState
local notation "V" => (dV).physicalState
local notation "XU" => (dU).physicalField
local notation "XV" => (dV).physicalField

open CutoffWordHistories RecursiveHeatBounds RecursiveHeatTargets Filter Topology

def leafMass (ν : Measure HeatCircle) (k : ℕ) : ℝ :=
  ∫ q : History HeatCircle k×Ω,JointUncutWordEvaluation.leaf L Λ U V XU XV k q.1 q.2 ∂(historyMeasure R ν k).prod μ

def referenceMass (ν : Measure HeatCircle) (k : ℕ) : ℝ :=
  ∫ q : History HeatCircle k×Ω,JointUncutWordEvaluation.reference L Λ U V XU XV k q.1 q.2 ∂(historyMeasure R ν k).prod μ

def markMass (ν : Measure HeatCircle) (k : ℕ) : ℝ :=
  ∫ q : History HeatCircle k×Ω,MixedJointUncutMark.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k q.1 q.2
    ∂(historyMeasure R ν k).prod μ

local notation "LM" => leafMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L
local notation "RM" => referenceMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L
local notation "MM" => markMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L

variable (T : ℝ) (hterm : ∀ x,L.terminal x=T)
variable (hstop : ∀ x,(L.observations.observations x 0).stop=T)
variable (htarget : ∀ x,(L.observations.observations x 0).target=T)
variable (hcenter : ∀ x,(L.observations.observations x 0).center=x)
local notation "ν" => AddCircle.haarAddCircle (T := 2*Real.pi)

local instance scalarRootUncutExpansion_inputSigma : MeasurableSpace RealHaarInput := borel _
local instance scalarRootUncutExpansion_inputBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance scalarRootUncutExpansion_bothSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance scalarRootUncutExpansion_bothBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
include hIJ₀ hIJ₁ hterm hstop htarget hcenter in
/-- The actual mixed joint finite first-defect expansion after removing
both recursively moving cutoffs. The ORIGINAL scalar root has stop equal to target, and its endpoint
is reached by the proved spatial L¹ heat limit. Constants are for each fixed smooth
coefficient and finite depth; no rough all-orders master is asserted. -/
theorem finite_expected_expansion (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J) (hΛ : 0≤Λ)
    (hA : R.totalVariance=(fun z => κ+aV z)) (hh : R.horizon≤(H:ℝ))
    (hT : R.base<T) (depth : ℕ) :
    LM ν 0=(∑ k∈Finset.range depth,RM ν k)+(∑ k∈Finset.range depth,MM ν k)+LM ν depth := by
  have hl0 := JointUncutEvaluationLimit.leaf_integral_tendsto L Λ U V XU XV
    (dU).physicalState_measurable (dV).physicalState_measurable (dU).physicalField_measurable (dV).physicalField_measurable ν μ 0
  have hld := JointUncutEvaluationLimit.leaf_integral_tendsto L Λ U V XU XV
    (dU).physicalState_measurable (dV).physicalState_measurable (dU).physicalField_measurable (dV).physicalField_measurable ν μ depth
  have hr := tendsto_finsetSum (Finset.range depth) (fun k _ =>
    JointUncutEvaluationLimit.reference_integral_tendsto L Λ U V XU XV
      (dU).physicalState_measurable (dV).physicalState_measurable (dU).physicalField_measurable (dV).physicalField_measurable ν μ k)
  have hm := tendsto_finsetSum (Finset.range depth) (fun k _ =>
    MixedJointUncutMark.mark_integral_tendsto 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hΛ ν k)
  have hc := tendsto_finsetSum (Finset.range depth) (fun k _ =>
    JointRecursiveCutoffCorrection.mass_tendsto_zero L Λ
      (dU).physicalState_measurable (dV).physicalState_measurable (dU).physicalField_measurable (dV).physicalField_measurable ν μ k)
  have ht := ((hr.add hm).add hc).add hld
  simp only [Finset.sum_const_zero,add_zero] at ht
  have he : (fun δ : ℝ => ∫ q : History HeatCircle 0×Ω,JointUncutEvaluationLimit.cutoffLeaf L Λ U V XU XV δ 0 q.1 q.2
      ∂(historyMeasure R ν 0).prod μ)=ᶠ[𝓝[>] (0:ℝ)]
      (fun δ => (∑ k∈Finset.range depth,∫ q : History HeatCircle k×Ω,JointUncutEvaluationLimit.cutoffReference L Λ U V XU XV δ k q.1 q.2
          ∂(historyMeasure R ν k).prod μ)+
        (∑ k∈Finset.range depth,∫ q : History HeatCircle k×Ω,MixedJointUncutMark.cutoffMark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ k q.1 q.2
          ∂(historyMeasure R ν k).prod μ)+
        (∑ k∈Finset.range depth,JointRecursiveCutoffCorrection.mass L Λ («U» := U) («V» := V) («XU» := XU) («XV» := XV) ν μ k δ)+
        ∫ q : History HeatCircle depth×Ω,JointUncutEvaluationLimit.cutoffLeaf L Λ U V XU XV δ depth q.1 q.2
          ∂(historyMeasure R ν depth).prod μ) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    change 0<δ at hδ
    have heq := ScalarRootFiniteExpansion.finite_expected_expansion 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      L T hterm hstop htarget hcenter J hIJ₀ hIJ₁ hnull hJ hΛ hA hh hT δ hδ depth
    simpa only [JointUncutEvaluationLimit.cutoffLeaf,JointUncutEvaluationLimit.cutoffReference,MixedJointUncutMark.cutoffMark,
      JointRecursiveCutoffCorrection.mass,dif_pos hδ,MixedJointZeroHeatExpectation.leafMass,
      MixedJointZeroHeatExpectation.referenceMass,MixedJointZeroHeatExpectation.markMass,
      RootMixedZeroHeatExpansion.correctionMass,JointZeroHeatCycle.correctionMass,MixedJointLevelData.leaf,
      MixedJointLevelData.reference] using heq
  exact tendsto_nhds_unique hl0 (ht.congr' he.symm)

end SHE.ScalarRootUncutExpansion
