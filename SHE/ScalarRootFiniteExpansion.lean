module

public import SHE.RootMixedZeroHeatExpansion
public import SHE.ScalarRootHeatLeaf
public import SHE.MixedJointZeroHeatExpectation
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

namespace SHE.ScalarRootFiniteExpansion
open MeasureTheory Set AddCircle PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation CutoffWordLevel
open GaussianTaylorAverage JointWordAnalytic
open scoped ENNReal NNReal
local instance scalarRootFiniteExpansionInstance1 : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance scalarRootFiniteExpansionInstance2 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance scalarRootFiniteExpansionInstance3 : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance scalarRootFiniteExpansionInstance4 : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance scalarRootFiniteExpansionInstance5 : MeasurableSpace CircleL2 := borel _
local instance scalarRootFiniteExpansionInstance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance scalarRootFiniteExpansionInstance7 : MeasurableSpace RealL2 := borel _
local instance scalarRootFiniteExpansionInstance8 : BorelSpace RealL2 := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
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

open CutoffWordHistories Filter Topology
variable (T : ℝ) (hterm : ∀ x,L.terminal x=T)
variable (hstop : ∀ x,(L.observations.observations x 0).stop=T)
variable (htarget : ∀ x,(L.observations.observations x 0).target=T)
variable (hcenter : ∀ x,(L.observations.observations x 0).center=x)

include hterm hstop htarget hcenter in
/-- The root-convergence premise of the recursive theorem is proved
for the actual scalar native endpoint, at every fixed time cutoff. -/
theorem root_converges (δ : ℝ) (hδ : 0<δ) :
    RootMixedZeroHeatExpectation.RootConverges 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ haarAddCircle := by
  have ht := ScalarRootHeatLeaf.integrated_root_difference_tendsto_zero
    L T hterm hstop htarget hcenter dU dV Λ
  unfold RootMixedZeroHeatExpectation.RootConverges RootJointHeatLeafLimit.leaf
  simp only [RootHeatBounds.level_zero]
  exact ht

local instance scalarRootFiniteExpansion_inputSigma : MeasurableSpace RealHaarInput := borel _
local instance scalarRootFiniteExpansion_inputBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance scalarRootFiniteExpansion_bothSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance scalarRootFiniteExpansion_bothBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ hterm hstop htarget hcenter in
/-- Exact actual mixed first-defect finite expansion with the ORIGINAL
root stop equal to its target. There is no supplied root-limit or gap
premise. Delta and each fixed smooth depth remain explicit. -/
theorem finite_expected_expansion (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J) (hΛ : 0≤Λ)
    (hA : R.totalVariance=(fun z => κ+aV z)) (hh : R.horizon≤(H:ℝ))
    (hT : R.base<T) (δ : ℝ) (hδ : 0<δ) (depth : ℕ) :
    MixedJointZeroHeatExpectation.leafMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ haarAddCircle 0 0=
      (∑ k∈Finset.range depth,MixedJointZeroHeatExpectation.referenceMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ haarAddCircle 0 k)+
      (∑ k∈Finset.range depth,MixedJointZeroHeatExpectation.markMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ haarAddCircle 0 k)+
      (∑ k∈Finset.range depth,RootMixedZeroHeatExpansion.correctionMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ haarAddCircle k)+
      MixedJointZeroHeatExpectation.leafMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ haarAddCircle 0 depth := by
  exact RootMixedZeroHeatExpansion.finite_expected_expansion
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ J hIJ₀ hIJ₁
    hnull hJ hΛ hA hh haarAddCircle (fun x => by rw [hterm x]; exact hT)
    (root_converges 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L T hterm hstop htarget hcenter δ hδ) depth

end SHE.ScalarRootFiniteExpansion

