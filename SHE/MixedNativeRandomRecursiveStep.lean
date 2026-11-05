module

public import SHE.MixedNativeRandomReferenceStep
public import SHE.ControlledReferenceRecursiveResidualBounds
public import SHE.ControlledReferenceRecursiveResidualContinuity
public import SHE.PastParameterHistoryExpectation

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false

namespace SHE.MixedNativeRandomRecursiveStep
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
local instance mixedNativeRandomRecursiveStep_circleSecondCountable : SecondCountableTopology StoppedFourier.CircleL2 :=
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
local instance mixedNativeRandomRecursiveStep_inputSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeRandomRecursiveStep_inputBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeRandomRecursiveStep_bothSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeRandomRecursiveStep_bothBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ hsmall in
/-- The true recursively changing word/reference family has conditional
first-defect cancellation at EVERY fixed finite depth. The canonical
reference at every node is determined by the ORIGINAL F_v states and
its applicability is derived from ordinary past locality of the SAME
full-H integral. The separate time and heat cutoffs are retained. -/
theorem integrated_residual_on_past_event (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J) (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hP : P.coefficient=(fun z => κ+aV z)) (hbH : b≤H)
    (hwindow : (b:ℝ)-(v:ℝ)≤P.horizon)
    (ε : ℝ≥0) (hε : 0<(ε:ℝ)) (hgap : ∀ i,(ε:ℝ)≤(Z i).target-(b:ℝ)) (k : ℕ)
    (ν : Measure (CutoffWordHistories.History Unit k)) [IsFiniteMeasure ν]
    (A : Set Ω) (hA : MeasurableSet[𝓕 v] A) :
    Integrable (fun q : CutoffWordHistories.History Unit k×Ω =>
      MixedJointPastExpectedLevel.noiseVersion 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        (L (pastParameter q.2) ε k) q.1 q.2) (ν.prod (μ.restrict A)) ∧
    (∫ q : CutoffWordHistories.History Unit k×Ω,
      MixedJointPastExpectedLevel.noiseVersion 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        (L (pastParameter q.2) ε k) q.1 q.2 ∂ν.prod (μ.restrict A))=0 := by
  let K := fun (p : Inputs) (q : CutoffWordHistories.History Unit k×Ω) =>
    MixedJointPastExpectedLevel.noiseVersion 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k) q.1 q.2
  obtain ⟨C,hCn,hC⟩ := ControlledReferenceRecursiveResidualBounds.uniform_piece_bounds 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF δ hδ hΛ k
  have hz : ∀ p h B,MeasurableSet[𝓕 v] B → (∫ ω in B,K p (h,ω) ∂μ)=0 := by
    intro p h B hB
    have hg : HeatCutoffHistories.Gap (L p ε k) (ε:ℝ) :=
      HeatCutoffHistories.iterate_gap (ControlledReferenceLevel.level P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF p)
        hδ ε.2 (fun _ => hgap) k
    exact (MixedJointPastExpectedLevel.noiseVersion_centered 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k)
      v rfl J hIJ₀ hIJ₁ hnull hJ hlocal hΛ rfl (by exact_mod_cast hbH) hε hg h B hB).2
  exact PastParameterHistoryExpectation.integral_random_on_event_eq_zero (𝓕 v) (𝓕.le v) μ ν K
    (fun p => MixedJointPastExpectedLevel.noiseVersion_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k))
    (fun q => ControlledReferenceRecursiveResidualContinuity.continuous_residual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε k q.1 q.2)
    (fun p q => (hC p ε q.1 q.2).2.2.2.2) hz
    (MixedNativeRandomReferenceStep.randomParameter_stronglyMeasurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v) A hA

end SHE.MixedNativeRandomRecursiveStep
