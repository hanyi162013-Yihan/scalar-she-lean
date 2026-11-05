module

public import SHE.MixedNativeRandomRecursiveIdentity
public import SHE.ControlledReferenceFamilySections
public import SHE.ControlledReferenceFamilyMark
public import SHE.ParameterIntegralSections
public import SHE.ControlledReferenceFamilyBackward
public import SHE.ControlledReferenceFamilyEvaluation
public import SHE.MixedJointUncutMark
public import SHE.ControlledReferenceUncutBounds
public import SHE.DominatedCutoffLimit
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

namespace SHE.ControlledReferenceFamilyResidual
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
local instance controlledReferenceFamilyResidual_circleSecondCountable : SecondCountableTopology StoppedFourier.CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput) := borel _
local instance : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)

open ControlledProfile ControlledReferenceLevel
variable (P : CanonicalCovariance.ProfileParameters) (hAs : SmoothCylinders.BoundedSmooth (fun z => κ+aV z))
variable (θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformSmooth.UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n => F q.1 q.2))


local notation "dU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U" => (dU).physicalState
local notation "V" => (dV).physicalState
local notation "XU" => (dU).physicalField
local notation "XV" => (dV).physicalField

variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

local notation "pastParameter" => MixedNativeRandomReferenceStep.randomParameter 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v

open Filter Topology
local notation "Base" => ControlledReferenceFamilyLevel.level P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF hFm

open CutoffWordHistories
local notation "LS" => ControlledReferenceFamilySections.leafSection 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF hFm
local notation "RS" => ControlledReferenceFamilySections.referenceSection 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF hFm
local notation "MS" => ControlledReferenceFamilySections.markSection 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF hFm

def residual (ν : Measure X) (depth : ℕ) (p : Inputs) (ω : Ω) : ℝ :=
  LS ν 0 p ω-(∑ k∈Finset.range depth,RS ν k p ω)-(∑ k∈Finset.range depth,MS ν k p ω)-LS ν depth p ω

local notation "K" => residual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF hFm

theorem residual_measurable (ν : Measure X) [IsFiniteMeasure ν] (depth : ℕ) (p : Inputs) :
    Measurable (K ν depth p) := by
  have hm (k : ℕ) := ControlledReferenceFamilySections.section_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm ν k p
  exact (((hm 0).1.sub (Finset.measurable_fun_sum _ (fun k _ => (hm k).2.1))).sub
    (Finset.measurable_fun_sum _ (fun k _ => (hm k).2.2))).sub (hm depth).1

include hsmall in
theorem residual_continuous (hΛ : 0≤Λ) (ν : Measure X) [IsFiniteMeasure ν] (depth : ℕ) (ω : Ω) :
    Continuous (fun p : Inputs => K ν depth p ω) := by
  have hc (k : ℕ) := ControlledReferenceFamilySections.section_continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hΛ ν k ω
  exact (((hc 0).1.sub (continuous_finsetSum _ (fun k _ => (hc k).2.1))).sub
    (continuous_finsetSum _ (fun k _ => (hc k).2.2))).sub (hc depth).1

private theorem sum_uniform {ι P₀ Ω₀ : Type*} (s : Finset ι) (f : ι→P₀→Ω₀→ℝ)
    (hb : ∀ i∈s,∃ C : ℝ,0≤C ∧ ∀ p ω,‖f i p ω‖≤C) :
    ∃ C : ℝ,0≤C ∧ ∀ p ω,‖∑ i∈s,f i p ω‖≤C := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0,le_rfl,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨C,hCn,hC⟩ := hb i (Finset.mem_insert_self _ _)
    obtain ⟨D,hDn,hD⟩ := ih (fun j hj => hb j (Finset.mem_insert_of_mem hj))
    refine ⟨C+D,add_nonneg hCn hDn,fun p ω => ?_⟩
    rw [Finset.sum_insert hi]
    exact (norm_add_le _ _).trans (add_le_add (hC p ω) (hD p ω))

theorem residual_bound (hΛ : 0≤Λ) (ν : Measure X) [IsFiniteMeasure ν] (depth : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ (p : Inputs) ω,‖K ν depth p ω‖≤C := by
  have hb (k : ℕ) := ControlledReferenceFamilySections.section_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hΛ ν k
  obtain ⟨A₀,hAn,hA₀⟩ := hb 0
  obtain ⟨Aₙ,hNn,hAₙ⟩ := hb depth
  obtain ⟨R₀,hRn,hR⟩ := sum_uniform (Finset.range depth) (fun k p ω => RS ν k p ω)
    (fun k _ => by obtain ⟨C,hCn,hC⟩ := hb k; exact ⟨C,hCn,fun p ω => (hC p ω).2.1⟩)
  obtain ⟨M₀,hMn,hM⟩ := sum_uniform (Finset.range depth) (fun k p ω => MS ν k p ω)
    (fun k _ => by obtain ⟨C,hCn,hC⟩ := hb k; exact ⟨C,hCn,fun p ω => (hC p ω).2.2⟩)
  refine ⟨A₀+R₀+M₀+Aₙ,by positivity,fun p ω => ?_⟩
  exact (norm_sub_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add (hA₀ p ω).1 (hR p ω))) (hM p ω)))
    (hAₙ p ω).1)

include hsmall in
/-- Exact finite-simple substitution of the ORIGINAL F_v states into
the integrated finite reference tree, once the deterministic-reference
conditional identities have been proved. All required continuity,
measurability and uniform domination come from the actual tree. -/
theorem random_residual_centered (hΛ : 0≤Λ) (ν : Measure X) [IsFiniteMeasure ν] (depth : ℕ)
    (hzero : ∀ p A,MeasurableSet[𝓕 v] A→(∫ ω in A,K ν depth p ω ∂μ)=0)
    (u : Ω→Inputs) (hu : StronglyMeasurable[𝓕 v] u)
    (A : Set Ω) (hA : MeasurableSet[𝓕 v] A) :
    Integrable (fun ω => K ν depth (u ω) ω) (μ.restrict A) ∧
      (∫ ω in A,K ν depth (u ω) ω ∂μ)=0 := by
  obtain ⟨C,hCn,hC⟩ := residual_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hΛ ν depth
  exact PastParameterSectionConditional.integral_random_on_event_eq_zero (𝓕 v) (𝓕.le v) μ
    (K ν depth)
    (residual_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF hFm ν depth)
    (fun _ => C) (integrable_const C) hC hzero hu
    (residual_continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hΛ ν depth)
    A hA

end SHE.ControlledReferenceFamilyResidual
