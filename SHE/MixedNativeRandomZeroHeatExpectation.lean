module

public import SHE.MixedNativeRandomRecursiveIdentity
public import SHE.MixedNativeRandomHeatAnalyticLimit
public import SHE.ControlledReferenceRandomHeatLeafLimit
public import SHE.FiniteWordExpectation
public import SHE.FiniteParameterL1Limit
public import SHE.JointRecursiveReferenceLimit
public import SHE.JointRecursiveRemainderConvergence
public import SHE.MixedJointMarkConvergence
public import SHE.ControlledReferenceRecursiveResidualBounds
public import SHE.ControlledReferenceRecursiveResidualContinuity
public import SHE.PastParameterHistoryExpectation

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false

namespace SHE.MixedNativeRandomZeroHeatExpectation
open MeasureTheory Set PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation CutoffWordLevel
open GaussianTaylorAverage JointWordAnalytic
open GaussianItoTest
open scoped ENNReal NNReal
local instance : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedNativeRandomZeroHeatExpectation_circleSecondCountable : SecondCountableTopology StoppedFourier.CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput) := borel _
local instance : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)

open ControlledProfile ControlledReferenceLevel
variable (P : CanonicalCovariance.ProfileParameters) (hAs : SmoothCylinders.BoundedSmooth (fun z => κ+aV z))
variable (θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)
variable (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hstop : ∀ i,(b:ℝ)≤(Z i).stop)
variable (F : WordRecursion.State n→ℝ) (hF : SmoothCylinders.BoundedSmooth F)
variable (δ : ℝ) (hδ : 0<δ)
local notation "L" => ControlledReferenceRecursiveBounds.level P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF δ hδ

local notation "dU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U" => (dU).physicalState
local notation "V" => (dV).physicalState
local notation "XU" => (dU).physicalField
local notation "XV" => (dV).physicalField

variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

local notation "pastParameter" => MixedNativeRandomReferenceStep.randomParameter 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Leaf" => (fun p ε k => MixedJointLevelData.leaf 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k))
local notation "Ref" => (fun p ε k => MixedJointLevelData.reference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k))
local notation "Loc" => (fun p ε k => MixedJointLevelData.localRemainder 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k))
local notation "Mark" => (fun p ε k => MixedJointLevelData.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k))

open Filter Topology
local notation "Base" => ControlledReferenceLevel.level P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF

local notation "R₀" => ControlledReferenceLevel.referenceData P (fun z => κ+aV z) hAs Λ θ v b hvb (0,0)

include hsmall in
/-- The entire actual random-reference recursive leaf converges in
history/sample L¹ as its separate heat age vanishes. This uses spatial
L² approximation for the newest physical leaf, not a fixed-point
zero-age observation identity. -/
theorem leaf_converges (hΛ : 0≤Λ) (ν : Measure Unit) [IsFiniteMeasure ν] (k : ℕ) (A : Set Ω) :
    Tendsto (fun ε : ℝ => ∫ q : CutoffWordHistories.History Unit k×Ω,
      Leaf (pastParameter q.2) ε.toNNReal k q.1 q.2 ∂(CutoffWordHistories.historyMeasure R₀ ν k).prod (μ.restrict A))
      (𝓝[>] (0:ℝ)) (𝓝 (∫ q : CutoffWordHistories.History Unit k×Ω,
        Leaf (pastParameter q.2) 0 k q.1 q.2 ∂(CutoffWordHistories.historyMeasure R₀ ν k).prod (μ.restrict A))) := by
  have hu := MixedNativeRandomReferenceStep.randomParameter_stronglyMeasurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
  have hum : StronglyMeasurable pastParameter := (hu.measurable.mono (𝓕.le v) le_rfl).stronglyMeasurable
  have ht := ControlledReferenceRandomHeatLeafLimit.integrated_leaf_difference_tendsto_zero P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall dU dV pastParameter hum hΛ ν k (μ.restrict A)
  have hi (ε : ℝ≥0) := (MixedNativeRandomRecursiveIdentity.pieces_integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε k (CutoffWordHistories.historyMeasure R₀ ν k) A).1
  exact FiniteWordExpectation.integral_tendsto_of_abs _ _ _ _ (hi 0) (fun ε => hi ε.toNNReal) ht

local instance mixedNativeRandomZeroHeatExpectation_inputSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeRandomZeroHeatExpectation_inputBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeRandomZeroHeatExpectation_bothSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeRandomZeroHeatExpectation_bothBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hsmall hIJ₀ hIJ₁ in
/-- The actual F_v-random-profile physical first-defect identity after
removing the recursive spatial regularization at fixed smooth depth.
The original full-H integral, ordinary past-event locality, positive
initial root gap, and the time cutoff are retained explicitly. -/
theorem expected_zero_heat_level (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J) (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hP : P.coefficient=(fun z => κ+aV z)) (hbH : b≤H)
    (hwindow : (b:ℝ)-(v:ℝ)≤P.horizon)
    (ν : Measure Unit) [IsFiniteMeasure ν] {η : ℝ} (hη : 0<η)
    (hgap : ∀ i,η≤(Z i).target-(b:ℝ)) (k : ℕ) (A : Set Ω) (hA : MeasurableSet[𝓕 v] A) :
    (∫ q : CutoffWordHistories.History Unit k×Ω,Leaf (pastParameter q.2) 0 k q.1 q.2
      ∂(CutoffWordHistories.historyMeasure R₀ ν k).prod (μ.restrict A))=
    (∫ q : CutoffWordHistories.History Unit k×Ω,Ref (pastParameter q.2) 0 k q.1 q.2
      ∂(CutoffWordHistories.historyMeasure R₀ ν k).prod (μ.restrict A))+
    (∫ q : CutoffWordHistories.History Unit k×Ω,Loc (pastParameter q.2) 0 k q.1 q.2
      ∂(CutoffWordHistories.historyMeasure R₀ ν k).prod (μ.restrict A))+
    (∫ q : CutoffWordHistories.History Unit k×Ω,Mark (pastParameter q.2) 0 k q.1 q.2
      ∂(CutoffWordHistories.historyMeasure R₀ ν k).prod (μ.restrict A)) := by
  have he : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ),
      (∫ q : CutoffWordHistories.History Unit k×Ω,Leaf (pastParameter q.2) ε.toNNReal k q.1 q.2
        ∂(CutoffWordHistories.historyMeasure R₀ ν k).prod (μ.restrict A))=
      (∫ q : CutoffWordHistories.History Unit k×Ω,Ref (pastParameter q.2) ε.toNNReal k q.1 q.2
        ∂(CutoffWordHistories.historyMeasure R₀ ν k).prod (μ.restrict A))+
      (∫ q : CutoffWordHistories.History Unit k×Ω,Loc (pastParameter q.2) ε.toNNReal k q.1 q.2
        ∂(CutoffWordHistories.historyMeasure R₀ ν k).prod (μ.restrict A))+
      (∫ q : CutoffWordHistories.History Unit k×Ω,Mark (pastParameter q.2) ε.toNNReal k q.1 q.2
        ∂(CutoffWordHistories.historyMeasure R₀ ν k).prod (μ.restrict A)) := by
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hη).filter_mono nhdsWithin_le_nhds] with ε hε hεη
    change 0<ε at hε
    have hc : ((ε.toNNReal:ℝ≥0):ℝ)=ε := Real.coe_toNNReal _ hε.le
    apply MixedNativeRandomRecursiveIdentity.expected_level 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall J hIJ₀ hIJ₁ hnull hJ hlocal hΛ hP hbH hwindow ε.toNNReal
    · simpa only [hc] using hε
    · intro i
      rw [hc]
      exact hεη.le.trans (hgap i)
    · exact hA
  have ht := ((MixedNativeRandomHeatAnalyticLimit.reference_converges 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ k (CutoffWordHistories.historyMeasure R₀ ν k) A).2.add
    (MixedNativeRandomHeatAnalyticLimit.remainder_converges 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ k (CutoffWordHistories.historyMeasure R₀ ν k) A).2).add
    (MixedNativeRandomHeatAnalyticLimit.mark_converges 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ k (CutoffWordHistories.historyMeasure R₀ ν k) A).2
  exact tendsto_nhds_unique (leaf_converges 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ν k A) (ht.congr' (Filter.EventuallyEq.symm he))

end SHE.MixedNativeRandomZeroHeatExpectation
