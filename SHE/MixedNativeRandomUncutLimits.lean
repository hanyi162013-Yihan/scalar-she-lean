module

public import SHE.MixedNativeRandomRecursiveIdentity
public import SHE.ControlledReferenceRandomCutoffEvaluationLimit
public import SHE.ControlledReferenceRandomCutoffCorrection
public import SHE.ControlledReferenceRandomMarkLimit
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

namespace SHE.MixedNativeRandomUncutLimits
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
local instance mixedNativeRandomUncutLimits_circleSecondCountable : SecondCountableTopology StoppedFourier.CircleL2 :=
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
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)
variable (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hstop : ∀ i,(b:ℝ)≤(Z i).stop)
variable (F : WordRecursion.State n→ℝ) (hF : SmoothCylinders.BoundedSmooth F)


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
local notation "Base" => ControlledReferenceLevel.level P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF

open CutoffWordHistories
local notation "R₀" => ControlledReferenceLevel.referenceData P (fun z => κ+aV z) hAs Λ θ v b hvb (0,0)

def leafMass (ν : Measure Unit) (k : ℕ) (A : Set Ω) : ℝ :=
  ∫ q : History Unit k×Ω,JointUncutWordEvaluation.leaf (Base (pastParameter q.2)) Λ U V XU XV k q.1 q.2
    ∂(historyMeasure R₀ ν k).prod (μ.restrict A)

def referenceMass (ν : Measure Unit) (k : ℕ) (A : Set Ω) : ℝ :=
  ∫ q : History Unit k×Ω,JointUncutWordEvaluation.reference (Base (pastParameter q.2)) Λ U V XU XV k q.1 q.2
    ∂(historyMeasure R₀ ν k).prod (μ.restrict A)

def markMass (ν : Measure Unit) (k : ℕ) (A : Set Ω) : ℝ :=
  ∫ q : History Unit k×Ω,MixedJointUncutMark.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    (Base (pastParameter q.2)) k q.1 q.2 ∂(historyMeasure R₀ ν k).prod (μ.restrict A)

def cutoffLeafMass (ν : Measure Unit) (k : ℕ) (A : Set Ω) (δ : ℝ) : ℝ :=
  ∫ q : History Unit k×Ω,JointUncutEvaluationLimit.cutoffLeaf (Base (pastParameter q.2)) Λ U V XU XV δ k q.1 q.2
    ∂(historyMeasure R₀ ν k).prod (μ.restrict A)

def cutoffReferenceMass (ν : Measure Unit) (k : ℕ) (A : Set Ω) (δ : ℝ) : ℝ :=
  ∫ q : History Unit k×Ω,JointUncutEvaluationLimit.cutoffReference (Base (pastParameter q.2)) Λ U V XU XV δ k q.1 q.2
    ∂(historyMeasure R₀ ν k).prod (μ.restrict A)

def cutoffMarkMass (ν : Measure Unit) (k : ℕ) (A : Set Ω) (δ : ℝ) : ℝ :=
  ∫ q : History Unit k×Ω,MixedJointUncutMark.cutoffMark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    (Base (pastParameter q.2)) δ k q.1 q.2 ∂(historyMeasure R₀ ν k).prod (μ.restrict A)

def correctionMass (ν : Measure Unit) (k : ℕ) (A : Set Ω) (δ : ℝ) : ℝ :=
  ControlledReferenceRandomCutoffCorrection.mass P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF
    U V XU XV pastParameter ν (μ.restrict A) k δ

local notation "LM" => leafMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF
local notation "RM" => referenceMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF
local notation "MM" => markMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF
local notation "CLM" => cutoffLeafMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF
local notation "CRM" => cutoffReferenceMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF
local notation "CMM" => cutoffMarkMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF
local notation "CM" => correctionMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF

include hsmall in
theorem leaf_tendsto (hΛ : 0≤Λ) (ν : Measure Unit) [IsFiniteMeasure ν] (k : ℕ) (A : Set Ω) :
    Tendsto (CLM ν k A) (𝓝[>] (0:ℝ)) (𝓝 (LM ν k A)) := by
  have hu := MixedNativeRandomReferenceStep.randomParameter_stronglyMeasurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
  have hum : StronglyMeasurable pastParameter := (hu.measurable.mono (𝓕.le v) le_rfl).stronglyMeasurable
  exact (ControlledReferenceRandomCutoffEvaluationLimit.leaf_converges P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF
    hsmall U V XU XV (dU).physicalState_measurable (dV).physicalState_measurable (dU).physicalField_measurable (dV).physicalField_measurable
    pastParameter hum hΛ ν (μ.restrict A) k).2

include hsmall in
theorem reference_tendsto (hΛ : 0≤Λ) (ν : Measure Unit) [IsFiniteMeasure ν] (k : ℕ) (A : Set Ω) :
    Tendsto (CRM ν k A) (𝓝[>] (0:ℝ)) (𝓝 (RM ν k A)) := by
  have hu := MixedNativeRandomReferenceStep.randomParameter_stronglyMeasurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
  have hum : StronglyMeasurable pastParameter := (hu.measurable.mono (𝓕.le v) le_rfl).stronglyMeasurable
  exact (ControlledReferenceRandomCutoffEvaluationLimit.reference_converges P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF
    hsmall U V XU XV (dU).physicalState_measurable (dV).physicalState_measurable (dU).physicalField_measurable (dV).physicalField_measurable
    pastParameter hum hΛ ν (μ.restrict A) k).2

include hsmall in
theorem mark_tendsto (hΛ : 0≤Λ) (ν : Measure Unit) [IsFiniteMeasure ν] (k : ℕ) (A : Set Ω) :
    Tendsto (CMM ν k A) (𝓝[>] (0:ℝ)) (𝓝 (MM ν k A)) := by
  have hu := MixedNativeRandomReferenceStep.randomParameter_stronglyMeasurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
  have hum : StronglyMeasurable pastParameter := (hu.measurable.mono (𝓕.le v) le_rfl).stronglyMeasurable
  exact ControlledReferenceRandomMarkLimit.mark_converges 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hsmall pastParameter hum hΛ ν (μ.restrict A) k

theorem correction_tendsto (ν : Measure Unit) [IsFiniteMeasure ν] (k : ℕ) (A : Set Ω) :
    Tendsto (CM ν k A) (𝓝[>] (0:ℝ)) (𝓝 0) :=
  ControlledReferenceRandomCutoffCorrection.mass_tendsto_zero P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF
    U V XU XV (dU).physicalState_measurable (dV).physicalState_measurable (dU).physicalField_measurable (dV).physicalField_measurable
    pastParameter ν (μ.restrict A) k

end SHE.MixedNativeRandomUncutLimits
