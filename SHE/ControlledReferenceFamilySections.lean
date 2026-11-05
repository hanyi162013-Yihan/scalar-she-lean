module

public import SHE.MixedNativeRandomRecursiveIdentity
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

namespace SHE.ControlledReferenceFamilySections
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
local instance controlledReferenceFamilySections_circleSecondCountable : SecondCountableTopology StoppedFourier.CircleL2 :=
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
local notation "R₀" => ControlledReferenceLevel.referenceData P (fun z => κ+aV z) hAs Λ θ v b hvb (0,0)
local notation "Leaf" => (fun p k h ω => JointUncutWordEvaluation.leaf (Base p) Λ U V XU XV k h ω)
local notation "Ref" => (fun p k h ω => JointUncutWordEvaluation.reference (Base p) Λ U V XU XV k h ω)
local notation "Mark" => (fun p k h ω => MixedJointUncutMark.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p) k h ω)

def leafSection (ν : Measure X) (k : ℕ) (p : Inputs) (ω : Ω) : ℝ :=
  ∫ h,Leaf p k h ω ∂historyMeasure R₀ ν k

def referenceSection (ν : Measure X) (k : ℕ) (p : Inputs) (ω : Ω) : ℝ :=
  ∫ h,Ref p k h ω ∂historyMeasure R₀ ν k

def markSection (ν : Measure X) (k : ℕ) (p : Inputs) (ω : Ω) : ℝ :=
  ∫ h,Mark p k h ω ∂historyMeasure R₀ ν k

local notation "LS" => leafSection 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF hFm
local notation "RS" => referenceSection 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF hFm
local notation "MS" => markSection 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF hFm

theorem section_measurable (ν : Measure X) [IsFiniteMeasure ν] (k : ℕ) (p : Inputs) :
    Measurable (LS ν k p) ∧ Measurable (RS ν k p) ∧ Measurable (MS ν k p) := by
  have hL := JointUncutWordEvaluation.leaf_measurable (Base p) Λ
    (dU).physicalState_measurable (dV).physicalState_measurable (dU).physicalField_measurable (dV).physicalField_measurable k
  have hR := JointUncutWordEvaluation.reference_measurable (Base p) Λ
    (dU).physicalState_measurable (dV).physicalState_measurable (dU).physicalField_measurable (dV).physicalField_measurable k
  have hM := MixedJointUncutMark.mark_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p) k
  exact ⟨(hL.stronglyMeasurable.integral_prod_left' (μ:=historyMeasure R₀ ν k)).measurable,
    (hR.stronglyMeasurable.integral_prod_left' (μ:=historyMeasure R₀ ν k)).measurable,
    (hM.stronglyMeasurable.integral_prod_left' (μ:=historyMeasure R₀ ν k)).measurable⟩

include hsmall in
/-- Genuine integrated uncut tree sections remain continuous in both
past inputs. Their domination is the actual common integrable history
weight, so random-profile substitution does not require a new input. -/
theorem section_continuous (hΛ : 0≤Λ) (ν : Measure X) [IsFiniteMeasure ν] (k : ℕ) (ω : Ω) :
    Continuous (fun p : Inputs => LS ν k p ω) ∧
    Continuous (fun p : Inputs => RS ν k p ω) ∧
    Continuous (fun p : Inputs => MS ν k p ω) := by
  let σ := historyMeasure R₀ ν k
  let W₀ := fun h : History X k => UncutSmoothWords.weight (Base (0,0)) k h
  have hW : Integrable W₀ σ := UncutHistoryMass.weight_integrable (Base (0,0)) ν k
  obtain ⟨C,hCn,hC⟩ := ControlledReferenceFamilyEvaluation.evaluation_bound P (fun z => κ+aV z) hAs Λ θ v b hvb
    Z htarget hstop F hF hFm U V XU XV k
  obtain ⟨B,hBn,hB⟩ := ControlledReferenceFamilyMark.mark_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hΛ k
  have hLm (p : Inputs) := JointUncutWordEvaluation.leaf_measurable (Base p) Λ
    (dU).physicalState_measurable (dV).physicalState_measurable (dU).physicalField_measurable (dV).physicalField_measurable k
  have hRm (p : Inputs) := JointUncutWordEvaluation.reference_measurable (Base p) Λ
    (dU).physicalState_measurable (dV).physicalState_measurable (dU).physicalField_measurable (dV).physicalField_measurable k
  have hMm (p : Inputs) := MixedJointUncutMark.mark_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p) k
  exact ⟨ParameterIntegralSections.section_continuous σ (fun p q => Leaf p k q.1 q.2) hLm
      (fun h => C*W₀ h) (hW.const_mul C) (fun p q => (hC p q.1 q.2).1)
      (fun q => ControlledReferenceFamilyEvaluation.leaf_parameter_continuous P (fun z => κ+aV z) hAs Λ θ v b hvb
        Z htarget hstop F hF hFm hsmall U V XU XV hΛ k q.1 q.2) ω,
    ParameterIntegralSections.section_continuous σ (fun p q => Ref p k q.1 q.2) hRm
      (fun h => C*W₀ h) (hW.const_mul C) (fun p q => (hC p q.1 q.2).2)
      (fun q => ControlledReferenceFamilyEvaluation.reference_parameter_continuous P (fun z => κ+aV z) hAs Λ θ v b hvb
        Z htarget hstop F hF hFm hsmall U V XU XV hΛ k q.1 q.2) ω,
    ParameterIntegralSections.section_continuous σ (fun p q => Mark p k q.1 q.2) hMm
      (fun h => B*W₀ h) (hW.const_mul B) (fun p q => hB p q.1 q.2)
      (fun q => ControlledReferenceFamilyMark.mark_parameter_continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hΛ k q.1 q.2) ω⟩

theorem section_bound (hΛ : 0≤Λ) (ν : Measure X) [IsFiniteMeasure ν] (k : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ (p : Inputs) ω,‖LS ν k p ω‖≤C ∧ ‖RS ν k p ω‖≤C ∧ ‖MS ν k p ω‖≤C := by
  let σ := historyMeasure R₀ ν k
  let W₀ := fun h : History X k => UncutSmoothWords.weight (Base (0,0)) k h
  have hW : Integrable W₀ σ := UncutHistoryMass.weight_integrable (Base (0,0)) ν k
  obtain ⟨C,hCn,hC⟩ := ControlledReferenceFamilyEvaluation.evaluation_bound P (fun z => κ+aV z) hAs Λ θ v b hvb
    Z htarget hstop F hF hFm U V XU XV k
  obtain ⟨B,hBn,hB⟩ := ControlledReferenceFamilyMark.mark_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hΛ k
  let K := max C B
  have hKn : 0≤K := hCn.trans (le_max_left _ _)
  have hWn : 0≤∫ h,W₀ h ∂σ := integral_nonneg (UncutSmoothWords.weight_nonneg (Base (0,0)) k)
  refine ⟨K*(∫ h,W₀ h ∂σ),mul_nonneg hKn hWn,fun p ω => ?_⟩
  have hbL (h : History X k) : ‖Leaf p k h ω‖≤K*W₀ h :=
    (hC p h ω).1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (UncutSmoothWords.weight_nonneg (Base (0,0)) k h))
  have hbR (h : History X k) : ‖Ref p k h ω‖≤K*W₀ h :=
    (hC p h ω).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (UncutSmoothWords.weight_nonneg (Base (0,0)) k h))
  have hbM (h : History X k) : ‖Mark p k h ω‖≤K*W₀ h :=
    (hB p h ω).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (UncutSmoothWords.weight_nonneg (Base (0,0)) k h))
  exact ⟨by simpa only [integral_const_mul,leafSection,referenceSection,markSection,σ] using norm_integral_le_of_norm_le (hW.const_mul K) (Eventually.of_forall hbL),
    by simpa only [integral_const_mul,leafSection,referenceSection,markSection,σ] using norm_integral_le_of_norm_le (hW.const_mul K) (Eventually.of_forall hbR),
    by simpa only [integral_const_mul,leafSection,referenceSection,markSection,σ] using norm_integral_le_of_norm_le (hW.const_mul K) (Eventually.of_forall hbM)⟩

include hsmall in
/-- Fubini identifies the integrated random-parameter sections with the
literal history/sample diagonal. No stochastic restart is introduced. -/
theorem diagonal_integrals (hΛ : 0≤Λ) (ν : Measure X) [IsFiniteMeasure ν]
    (τ : Measure Ω) [IsFiniteMeasure τ] (u : Ω→Inputs) (hu : StronglyMeasurable u) (k : ℕ) :
    (∫ ω,LS ν k (u ω) ω ∂τ)=
      (∫ q : History X k×Ω,Leaf (u q.2) k q.1 q.2 ∂(historyMeasure R₀ ν k).prod τ) ∧
    (∫ ω,RS ν k (u ω) ω ∂τ)=
      (∫ q : History X k×Ω,Ref (u q.2) k q.1 q.2 ∂(historyMeasure R₀ ν k).prod τ) ∧
    (∫ ω,MS ν k (u ω) ω ∂τ)=
      (∫ q : History X k×Ω,Mark (u q.2) k q.1 q.2 ∂(historyMeasure R₀ ν k).prod τ) := by
  let σ := historyMeasure R₀ ν k
  let W₀ := fun q : History X k×Ω => UncutSmoothWords.weight (Base (0,0)) k q.1
  have hW : Integrable W₀ (σ.prod τ) := (UncutHistoryMass.weight_integrable (Base (0,0)) ν k).comp_fst τ
  obtain ⟨C,hCn,hC⟩ := ControlledReferenceFamilyEvaluation.evaluation_bound P (fun z => κ+aV z) hAs Λ θ v b hvb
    Z htarget hstop F hF hFm U V XU XV k
  obtain ⟨B,hBn,hB⟩ := ControlledReferenceFamilyMark.mark_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hΛ k
  have hm := ControlledReferenceFamilyEvaluation.diagonal_measurable P (fun z => κ+aV z) hAs Λ θ v b hvb
    Z htarget hstop F hF hFm hsmall U V XU XV
    (dU).physicalState_measurable (dV).physicalState_measurable (dU).physicalField_measurable (dV).physicalField_measurable hΛ u hu k
  have hmM := ControlledReferenceFamilyMark.diagonal_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hΛ u hu k
  have hiL : Integrable (fun q : History X k×Ω => Leaf (u q.2) k q.1 q.2) (σ.prod τ) :=
    (hW.const_mul C).mono' hm.1.aestronglyMeasurable (Eventually.of_forall (fun q => (hC (u q.2) q.1 q.2).1))
  have hiR : Integrable (fun q : History X k×Ω => Ref (u q.2) k q.1 q.2) (σ.prod τ) :=
    (hW.const_mul C).mono' hm.2.aestronglyMeasurable (Eventually.of_forall (fun q => (hC (u q.2) q.1 q.2).2))
  have hiM : Integrable (fun q : History X k×Ω => Mark (u q.2) k q.1 q.2) (σ.prod τ) :=
    (hW.const_mul B).mono' hmM.aestronglyMeasurable (Eventually.of_forall (fun q => hB (u q.2) q.1 q.2))
  exact ⟨(integral_prod_symm _ hiL).symm,(integral_prod_symm _ hiR).symm,(integral_prod_symm _ hiM).symm⟩

end SHE.ControlledReferenceFamilySections
