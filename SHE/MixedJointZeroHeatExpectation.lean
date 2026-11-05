module

public import SHE.MixedJointMarkConvergence
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

namespace SHE.MixedJointZeroHeatExpectation
open MeasureTheory Set PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation CutoffWordLevel
open GaussianTaylorAverage JointWordAnalytic
open scoped ENNReal NNReal
local instance mixedJointZeroHeatExpectationInstance1 : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance mixedJointZeroHeatExpectationInstance2 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedJointZeroHeatExpectationInstance3 : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance mixedJointZeroHeatExpectationInstance4 : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance mixedJointZeroHeatExpectationInstance5 : MeasurableSpace CircleL2 := borel _
local instance mixedJointZeroHeatExpectationInstance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedJointZeroHeatExpectationInstance7 : MeasurableSpace RealL2 := borel _
local instance mixedJointZeroHeatExpectationInstance8 : BorelSpace RealL2 := ⟨rfl⟩
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

local notation "Lleaf" => MixedJointLevelData.leaf 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "Lref" => MixedJointLevelData.reference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "Lrem" => MixedJointLevelData.localRemainder 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "Lmark" => MixedJointLevelData.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S

def leafMass (ν : Measure P) (ε : ℝ≥0) (k : ℕ) : ℝ :=
  ∫ q : History P k×Ω,Lleaf (level L δ hδ ε k) q.1 q.2 ∂(historyMeasure R ν k).prod μ

def referenceMass (ν : Measure P) (ε : ℝ≥0) (k : ℕ) : ℝ :=
  ∫ q : History P k×Ω,Lref (level L δ hδ ε k) q.1 q.2 ∂(historyMeasure R ν k).prod μ

def remainderMass (ν : Measure P) (ε : ℝ≥0) (k : ℕ) : ℝ :=
  ∫ q : History P k×Ω,Lrem (level L δ hδ ε k) q.1 q.2 ∂(historyMeasure R ν k).prod μ

def markMass (ν : Measure P) (ε : ℝ≥0) (k : ℕ) : ℝ :=
  ∫ q : History P k×Ω,Lmark (level L δ hδ ε k) q.1 q.2 ∂(historyMeasure R ν k).prod μ

local notation "LM" => leafMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ
local notation "RM" => referenceMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ
local notation "AM" => remainderMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ
local notation "MM" => markMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ

theorem leafMass_tendsto (ν : Measure P) [IsFiniteMeasure ν] (k : ℕ) :
    Tendsto (fun ε : ℝ => LM ν ε.toNNReal k) (𝓝[>] (0:ℝ)) (𝓝 (LM ν 0 k)) := by
  obtain ⟨C,_,hC⟩ := (test_uniform L δ hδ k).norm_bound
  have hi (ε : ℝ≥0) : Integrable (fun q : History P k×Ω => Lleaf (level L δ hδ ε k) q.1 q.2)
      ((historyMeasure R ν k).prod μ) :=
    (integrable_const C).mono'
      (MixedJointLevelData.leaf_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (level L δ hδ ε k)).aestronglyMeasurable
      (Eventually.of_forall (fun q => hC (ε,q.1) _))
  exact FiniteWordExpectation.integral_tendsto_of_abs _ _ _ _ (hi 0) (fun ε => hi ε.toNNReal)
    (JointHeatLeafLimit.integrated_leaf_difference_tendsto_zero L δ hδ dU dV Λ ν k)

theorem referenceMass_tendsto (ν : Measure P) [IsFiniteMeasure ν] (k : ℕ) :
    Tendsto (fun ε : ℝ => RM ν ε.toNNReal k) (𝓝[>] (0:ℝ)) (𝓝 (RM ν 0 k)) := by
  obtain ⟨C,_,hC⟩ := (test_uniform L δ hδ k).norm_bound
  have hi (ε : ℝ≥0) : Integrable (fun q : History P k×Ω => Lref (level L δ hδ ε k) q.1 q.2)
      ((historyMeasure R ν k).prod μ) := by
    apply (integrable_const C).mono'
      (MixedJointLevelData.reference_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (level L δ hδ ε k)).aestronglyMeasurable
    filter_upwards with q
    exact GaussianSmooth.average_norm_bound _ (hC (ε,q.1)) _
  exact FiniteWordExpectation.integral_tendsto_of_abs _ _ _ _ (hi 0) (fun ε => hi ε.toNNReal)
    (JointRecursiveReferenceLimit.integrated_reference_difference_tendsto_zero L δ hδ Λ U V XU XV
      (dU).physicalState_measurable (dV).physicalState_measurable (dU).physicalField_measurable (dV).physicalField_measurable ν μ k)

theorem remainderMass_tendsto (ν : Measure P) [IsFiniteMeasure ν] (k : ℕ) :
    Tendsto (fun ε : ℝ => AM ν ε.toNNReal k) (𝓝[>] (0:ℝ)) (𝓝 (AM ν 0 k)) := by
  obtain ⟨C,_,hC⟩ := JointRecursiveRemainderConvergence.uniform_remainder_bound L δ hδ Λ U V XU XV k
  have hi (ε : ℝ≥0) : Integrable (fun q : History P k×Ω => Lrem (level L δ hδ ε k) q.1 q.2)
      ((historyMeasure R ν k).prod μ) :=
    (integrable_const C).mono'
      (MixedJointLevelData.localRemainder_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (level L δ hδ ε k)).aestronglyMeasurable
      (Eventually.of_forall (fun q => hC ε q.1 q.2))
  exact FiniteWordExpectation.integral_tendsto_of_abs _ _ _ _ (hi 0) (fun ε => hi ε.toNNReal)
    (JointRecursiveRemainderConvergence.integrated_remainder_difference_tendsto_zero L δ hδ Λ U V XU XV
      (dU).physicalState_measurable (dV).physicalState_measurable (dU).physicalField_measurable (dV).physicalField_measurable ν μ k)

theorem markMass_tendsto (hΛ : 0≤Λ) (ν : Measure P) [IsFiniteMeasure ν] (k : ℕ) :
    Tendsto (fun ε : ℝ => MM ν ε.toNNReal k) (𝓝[>] (0:ℝ)) (𝓝 (MM ν 0 k)) := by
  obtain ⟨C,_,hC⟩ := MixedJointMarkConvergence.uniform_mark_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ hΛ k
  have hi (ε : ℝ≥0) : Integrable (fun q : History P k×Ω => Lmark (level L δ hδ ε k) q.1 q.2)
      ((historyMeasure R ν k).prod μ) :=
    (integrable_const C).mono'
      (MixedJointLevelData.mark_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (level L δ hδ ε k)).aestronglyMeasurable
      (Eventually.of_forall (fun q => hC ε q.1 q.2))
  exact FiniteWordExpectation.integral_tendsto_of_abs _ _ _ _ (hi 0) (fun ε => hi ε.toNNReal)
    (MixedJointMarkConvergence.integrated_mark_difference_tendsto_zero 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ hΛ ν k)

local instance mixedJointZeroHeatExpectation_inputSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedJointZeroHeatExpectation_inputBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedJointZeroHeatExpectation_bothSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedJointZeroHeatExpectation_bothBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
include hIJ₀ hIJ₁ in
/-- Literal actual mixed-pair first-defect expectation identity after
removing spatial regularization at the actual moving finite word level.
No pointwise zero-age Ito formula or restart theorem is assumed. -/
theorem expected_zero_heat_level (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J) (hΛ : 0≤Λ)
    (hA : R.totalVariance=(fun z => κ+aV z)) (hh : R.horizon≤(H:ℝ))
    (ν : Measure P) [IsFiniteMeasure ν] {η : ℝ} (hη : 0<η)
    (hgap : HeatCutoffHistories.Gap L η) (k : ℕ) :
    LM ν 0 k=RM ν 0 k+AM ν 0 k+MM ν 0 k := by
  have he : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ),LM ν ε.toNNReal k=RM ν ε.toNNReal k+AM ν ε.toNNReal k+MM ν ε.toNNReal k := by
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hη).filter_mono nhdsWithin_le_nhds] with ε hε hεη
    have hecoe : ((ε.toNNReal:ℝ≥0):ℝ)=ε := Real.coe_toNNReal _ hε.le
    have heg : HeatCutoffHistories.Gap L (ε.toNNReal:ℝ) := by
      intro p i
      rw [hecoe]
      exact hεη.le.trans (hgap p i)
    have hge : HeatCutoffHistories.Gap (level L δ hδ ε.toNNReal k) ε := by
      have hhg := HeatCutoffHistories.iterate_gap L hδ ε.toNNReal.2 heg k
      intro p i
      exact hecoe.symm.le.trans (hhg p i)
    exact MixedJointIntegratedLevel.expected_level 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (level L δ hδ ε.toNNReal k) J hIJ₀ hIJ₁ hnull hJ hΛ hA hh
      hε hge (historyMeasure R ν k)
  have ht := ((referenceMass_tendsto 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ ν k).add
    (remainderMass_tendsto 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ ν k)).add
    (markMass_tendsto 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ hΛ ν k)
  have he' : (fun ε : ℝ => LM ν ε.toNNReal k)=ᶠ[𝓝[>] (0:ℝ)]
      (fun ε => RM ν ε.toNNReal k+AM ν ε.toNNReal k+MM ν ε.toNNReal k) := he
  exact tendsto_nhds_unique (leafMass_tendsto 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ ν k)
    (ht.congr' he'.symm)

end SHE.MixedJointZeroHeatExpectation
