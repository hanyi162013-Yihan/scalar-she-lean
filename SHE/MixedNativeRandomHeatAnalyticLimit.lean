module

public import SHE.MixedNativeRandomRecursiveIdentity
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

namespace SHE.MixedNativeRandomHeatAnalyticLimit
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
local instance mixedNativeRandomHeatAnalyticLimit_circleSecondCountable : SecondCountableTopology StoppedFourier.CircleL2 :=
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

include hsmall in
/-- Genuine full history/sample L¹ and expected-value convergence of
the actual random-past-reference reference as the separate spatial heat
age vanishes. The entire recursive word depends on ε and the ORIGINAL
F_v states; δ and smooth finite depth remain fixed. -/
theorem reference_converges (hΛ : 0≤Λ) (k : ℕ)
    (ν : Measure (CutoffWordHistories.History Unit k)) [IsFiniteMeasure ν] (A : Set Ω) :
    Tendsto (fun ε : ℝ => ∫ q : CutoffWordHistories.History Unit k×Ω,
      |Ref (pastParameter q.2) ε.toNNReal k q.1 q.2-Ref (pastParameter q.2) 0 k q.1 q.2| ∂ν.prod (μ.restrict A))
      (𝓝[>] (0:ℝ)) (𝓝 0) ∧
    Tendsto (fun ε : ℝ => ∫ q : CutoffWordHistories.History Unit k×Ω,
      Ref (pastParameter q.2) ε.toNNReal k q.1 q.2 ∂ν.prod (μ.restrict A))
      (𝓝[>] (0:ℝ)) (𝓝 (∫ q : CutoffWordHistories.History Unit k×Ω,
        Ref (pastParameter q.2) 0 k q.1 q.2 ∂ν.prod (μ.restrict A))) := by
  obtain ⟨C,hCn,hC⟩ := ControlledReferenceRecursiveResidualBounds.uniform_piece_bounds 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF δ hδ hΛ k
  let g := fun (ε : ℝ≥0) (q : CutoffWordHistories.History Unit k×Ω) => Ref (pastParameter q.2) ε k q.1 q.2
  have hm (ε : ℝ≥0) : AEStronglyMeasurable (g ε) (ν.prod (μ.restrict A)) :=
    (MixedNativeRandomRecursiveIdentity.pieces_integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε k ν A).2.1.aestronglyMeasurable
  have hb (ε : ℝ≥0) (q : CutoffWordHistories.History Unit k×Ω) : ‖g ε q‖≤C :=
    (hC (pastParameter q.2) ε q.1 q.2).2.1
  have hc (q : CutoffWordHistories.History Unit k×Ω) : Continuous (fun ε => g ε q) := by
    have hh := JointRecursiveReferenceLimit.continuous_reference (Base (pastParameter q.2)) δ hδ Λ U V XU XV k q.1 q.2
    exact hh
  exact ⟨FiniteParameterL1Limit.bounded_continuous_L1 (ν.prod (μ.restrict A)) g hm hb hc,
    FiniteParameterL1Limit.bounded_continuous_integral (ν.prod (μ.restrict A)) g hm hb hc⟩

include hsmall in
/-- Genuine full history/sample L¹ and expected-value convergence of
the actual random-past-reference remainder as the separate spatial heat
age vanishes. The entire recursive word depends on ε and the ORIGINAL
F_v states; δ and smooth finite depth remain fixed. -/
theorem remainder_converges (hΛ : 0≤Λ) (k : ℕ)
    (ν : Measure (CutoffWordHistories.History Unit k)) [IsFiniteMeasure ν] (A : Set Ω) :
    Tendsto (fun ε : ℝ => ∫ q : CutoffWordHistories.History Unit k×Ω,
      |Loc (pastParameter q.2) ε.toNNReal k q.1 q.2-Loc (pastParameter q.2) 0 k q.1 q.2| ∂ν.prod (μ.restrict A))
      (𝓝[>] (0:ℝ)) (𝓝 0) ∧
    Tendsto (fun ε : ℝ => ∫ q : CutoffWordHistories.History Unit k×Ω,
      Loc (pastParameter q.2) ε.toNNReal k q.1 q.2 ∂ν.prod (μ.restrict A))
      (𝓝[>] (0:ℝ)) (𝓝 (∫ q : CutoffWordHistories.History Unit k×Ω,
        Loc (pastParameter q.2) 0 k q.1 q.2 ∂ν.prod (μ.restrict A))) := by
  obtain ⟨C,hCn,hC⟩ := ControlledReferenceRecursiveResidualBounds.uniform_piece_bounds 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF δ hδ hΛ k
  let g := fun (ε : ℝ≥0) (q : CutoffWordHistories.History Unit k×Ω) => Loc (pastParameter q.2) ε k q.1 q.2
  have hm (ε : ℝ≥0) : AEStronglyMeasurable (g ε) (ν.prod (μ.restrict A)) :=
    (MixedNativeRandomRecursiveIdentity.pieces_integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε k ν A).2.2.1.aestronglyMeasurable
  have hb (ε : ℝ≥0) (q : CutoffWordHistories.History Unit k×Ω) : ‖g ε q‖≤C :=
    (hC (pastParameter q.2) ε q.1 q.2).2.2.1
  have hc (q : CutoffWordHistories.History Unit k×Ω) : Continuous (fun ε => g ε q) := by
    have hh := JointRecursiveRemainderConvergence.continuous_remainder (Base (pastParameter q.2)) δ hδ Λ U V XU XV (dU).physicalState_measurable (dV).physicalState_measurable (dU).physicalField_measurable (dV).physicalField_measurable k q.1 q.2
    exact hh
  exact ⟨FiniteParameterL1Limit.bounded_continuous_L1 (ν.prod (μ.restrict A)) g hm hb hc,
    FiniteParameterL1Limit.bounded_continuous_integral (ν.prod (μ.restrict A)) g hm hb hc⟩

include hsmall in
/-- Genuine full history/sample L¹ and expected-value convergence of
the actual random-past-reference mark as the separate spatial heat
age vanishes. The entire recursive word depends on ε and the ORIGINAL
F_v states; δ and smooth finite depth remain fixed. -/
theorem mark_converges (hΛ : 0≤Λ) (k : ℕ)
    (ν : Measure (CutoffWordHistories.History Unit k)) [IsFiniteMeasure ν] (A : Set Ω) :
    Tendsto (fun ε : ℝ => ∫ q : CutoffWordHistories.History Unit k×Ω,
      |Mark (pastParameter q.2) ε.toNNReal k q.1 q.2-Mark (pastParameter q.2) 0 k q.1 q.2| ∂ν.prod (μ.restrict A))
      (𝓝[>] (0:ℝ)) (𝓝 0) ∧
    Tendsto (fun ε : ℝ => ∫ q : CutoffWordHistories.History Unit k×Ω,
      Mark (pastParameter q.2) ε.toNNReal k q.1 q.2 ∂ν.prod (μ.restrict A))
      (𝓝[>] (0:ℝ)) (𝓝 (∫ q : CutoffWordHistories.History Unit k×Ω,
        Mark (pastParameter q.2) 0 k q.1 q.2 ∂ν.prod (μ.restrict A))) := by
  obtain ⟨C,hCn,hC⟩ := ControlledReferenceRecursiveResidualBounds.uniform_piece_bounds 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF δ hδ hΛ k
  let g := fun (ε : ℝ≥0) (q : CutoffWordHistories.History Unit k×Ω) => Mark (pastParameter q.2) ε k q.1 q.2
  have hm (ε : ℝ≥0) : AEStronglyMeasurable (g ε) (ν.prod (μ.restrict A)) :=
    (MixedNativeRandomRecursiveIdentity.pieces_integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε k ν A).2.2.2.aestronglyMeasurable
  have hb (ε : ℝ≥0) (q : CutoffWordHistories.History Unit k×Ω) : ‖g ε q‖≤C :=
    (hC (pastParameter q.2) ε q.1 q.2).2.2.2.1
  have hc (q : CutoffWordHistories.History Unit k×Ω) : Continuous (fun ε => g ε q) := by
    have hh := MixedJointMarkConvergence.continuous_mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base (pastParameter q.2)) δ hδ hΛ k q.1 q.2
    exact hh
  exact ⟨FiniteParameterL1Limit.bounded_continuous_L1 (ν.prod (μ.restrict A)) g hm hb hc,
    FiniteParameterL1Limit.bounded_continuous_integral (ν.prod (μ.restrict A)) g hm hb hc⟩

end SHE.MixedNativeRandomHeatAnalyticLimit
