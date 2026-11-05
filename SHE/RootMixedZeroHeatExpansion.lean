module

public import SHE.RootMixedZeroHeatExpectation
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

namespace SHE.RootMixedZeroHeatExpansion
open MeasureTheory Set PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation CutoffWordLevel
open GaussianTaylorAverage JointWordAnalytic
open scoped ENNReal NNReal
local instance rootMixedZeroHeatExpansionInstance1 : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance rootMixedZeroHeatExpansionInstance2 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance rootMixedZeroHeatExpansionInstance3 : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance rootMixedZeroHeatExpansionInstance4 : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance rootMixedZeroHeatExpansionInstance5 : MeasurableSpace CircleL2 := borel _
local instance rootMixedZeroHeatExpansionInstance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance rootMixedZeroHeatExpansionInstance7 : MeasurableSpace RealL2 := borel _
local instance rootMixedZeroHeatExpansionInstance8 : BorelSpace RealL2 := ⟨rfl⟩
variable {Ω P : Type*} [MeasurableSpace Ω] [MeasurableSpace P]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {R : ReferenceData} {n : ℕ} (L : Level R P n)
local notation "dU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U" => (dU).physicalState
local notation "V" => (dV).physicalState
local notation "XU" => (dU).physicalField
local notation "XV" => (dV).physicalField

open CutoffWordHistories RecursiveHeatBounds RecursiveHeatTargets Filter Topology
variable (δ : ℝ) (hδ : 0<δ)

local notation "LM" => MixedJointZeroHeatExpectation.leafMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ
local notation "RM" => MixedJointZeroHeatExpectation.referenceMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ
local notation "AM" => MixedJointZeroHeatExpectation.remainderMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ
local notation "MM" => MixedJointZeroHeatExpectation.markMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ

def correctionMass (ν : Measure P) (k : ℕ) : ℝ :=
  JointZeroHeatCycle.correctionMass L δ hδ dU dV Λ ν k

local notation "CM" => correctionMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ
local instance rootMixedZeroHeatExpansion_inputSigma : MeasurableSpace RealHaarInput := borel _
local instance rootMixedZeroHeatExpansion_inputBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance rootMixedZeroHeatExpansion_bothSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance rootMixedZeroHeatExpansion_bothBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
include hIJ₀ hIJ₁ in
/-- Exact finite mixed first-defect expansion after the genuine moving
spatial heat cutoff limit. Only scalar insertions recurse; every actual
common-Haar defect terminates its branch. Delta remains explicit. -/
theorem finite_expected_expansion (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J) (hΛ : 0≤Λ)
    (hA : R.totalVariance=(fun z => κ+aV z)) (hh : R.horizon≤(H:ℝ))
    (ν : Measure P) [IsFiniteMeasure ν] (hstart : ∀ p,R.base<L.terminal p)
    (hroot : RootMixedZeroHeatExpectation.RootConverges 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ ν) (depth : ℕ) :
    LM ν 0 0=(∑ k∈Finset.range depth,RM ν 0 k)+(∑ k∈Finset.range depth,MM ν 0 k)+
      (∑ k∈Finset.range depth,CM ν k)+LM ν 0 depth := by
  have hs (k : ℕ) : LM ν 0 k=RM ν 0 k+MM ν 0 k+CM ν k+LM ν 0 (k+1) := by
    have he0 := RootMixedZeroHeatExpectation.expected_zero_heat_level 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      L δ hδ J hIJ₀ hIJ₁ hnull hJ hΛ hA hh ν hstart hroot k
    have he : LM ν 0 k=RM ν 0 k+AM ν 0 k+MM ν 0 k := by
      simpa only [RootMixedZeroHeatExpectation.leafMass,RootMixedZeroHeatExpectation.referenceMass,
        RootMixedZeroHeatExpectation.remainderMass,RootMixedZeroHeatExpectation.markMass,
        MixedJointZeroHeatExpectation.leafMass,MixedJointZeroHeatExpectation.referenceMass,
        MixedJointZeroHeatExpectation.remainderMass,MixedJointZeroHeatExpectation.markMass,
        RootHeatBounds.level_zero] using he0
    have hc := JointZeroHeatCycle.correctionMass_eq L δ hδ dU dV Λ ν k
    change CM ν k=AM ν 0 k-LM ν 0 (k+1) at hc
    linarith only [he,hc]
  induction depth with
  | zero => simp
  | succ d ih =>
    simp only [Finset.sum_range_succ]
    linarith only [ih,hs d]

end SHE.RootMixedZeroHeatExpansion
