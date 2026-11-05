module

public import SHE.MixedNativeRandomRecursiveStep
public import SHE.ControlledReferenceRecursiveResidualBounds
public import SHE.ControlledReferenceRecursiveResidualContinuity
public import SHE.PastParameterHistoryExpectation

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false

namespace SHE.MixedNativeRandomRecursiveIdentity
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
local instance mixedNativeRandomRecursiveIdentity_circleSecondCountable : SecondCountableTopology StoppedFourier.CircleL2 :=
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

include hsmall in
theorem pieces_integrable (hΛ : 0≤Λ) (ε : ℝ≥0) (k : ℕ)
    (ν : Measure (CutoffWordHistories.History Unit k)) [IsFiniteMeasure ν] (A : Set Ω) :
    Integrable (fun q : CutoffWordHistories.History Unit k×Ω => Leaf (pastParameter q.2) ε k q.1 q.2) (ν.prod (μ.restrict A)) ∧
    Integrable (fun q : CutoffWordHistories.History Unit k×Ω => Ref (pastParameter q.2) ε k q.1 q.2) (ν.prod (μ.restrict A)) ∧
    Integrable (fun q : CutoffWordHistories.History Unit k×Ω => Loc (pastParameter q.2) ε k q.1 q.2) (ν.prod (μ.restrict A)) ∧
    Integrable (fun q : CutoffWordHistories.History Unit k×Ω => Mark (pastParameter q.2) ε k q.1 q.2) (ν.prod (μ.restrict A)) := by
  obtain ⟨C,hCn,hC⟩ := ControlledReferenceRecursiveResidualBounds.uniform_piece_bounds 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF δ hδ hΛ k
  have hu := MixedNativeRandomReferenceStep.randomParameter_stronglyMeasurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
  let Γ := CutoffWordHistories.History Unit k
  let mΓ : MeasurableSpace Γ := inferInstance
  have hmprod : mΓ.prod (𝓕 v)≤mΓ.prod ‹MeasurableSpace Ω› :=
    sup_le_sup le_rfl (MeasurableSpace.comap_mono (𝓕.le v))
  have huprod : @StronglyMeasurable (Γ×Ω) Inputs _ (mΓ.prod (𝓕 v)) (fun q => pastParameter q.2) :=
    hu.comp_measurable measurable_snd
  have diagonal (K : Inputs→Γ×Ω→ℝ) (hK : ∀ p,Measurable (K p))
      (hc : ∀ q,Continuous (fun p => K p q)) (hb : ∀ p q,‖K p q‖≤C) :
      Integrable (fun q : Γ×Ω => K (pastParameter q.2) q) (ν.prod (μ.restrict A)) := by
    have hm := PastParameterDiagonal.stronglyMeasurable_diagonal (mΓ.prod (𝓕 v)) hmprod K hK huprod hc
    exact (integrable_const C).mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun q => hb (pastParameter q.2) q))
  have hlc (q : Γ×Ω) := ControlledReferenceRecursiveFields.continuous_leaf P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall
    U V XU XV hΛ ε k q.1 q.2
  have hrc (q : Γ×Ω) := ControlledReferenceRecursiveFields.continuous_reference P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall
    U V XU XV hΛ ε k q.1 q.2
  have hcc (q : Γ×Ω) := ControlledReferenceRecursiveRemainder.continuous_remainder P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall
    U V XU XV (dU).physicalState_measurable (dV).physicalState_measurable
    (dU).physicalField_measurable (dV).physicalField_measurable hΛ ε k q.1 q.2
  have hmc (q : Γ×Ω) := ControlledReferenceRecursiveResidualContinuity.continuous_mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε k q.1 q.2
  exact ⟨diagonal (fun p q => Leaf p ε k q.1 q.2)
      (fun p => MixedJointLevelData.leaf_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k)) hlc
      (fun p q => (hC p ε q.1 q.2).1),
    diagonal (fun p q => Ref p ε k q.1 q.2)
      (fun p => MixedJointLevelData.reference_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k)) hrc
      (fun p q => (hC p ε q.1 q.2).2.1),
    diagonal (fun p q => Loc p ε k q.1 q.2)
      (fun p => MixedJointLevelData.localRemainder_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k)) hcc
      (fun p q => (hC p ε q.1 q.2).2.2.1),
    diagonal (fun p q => Mark p ε k q.1 q.2)
      (fun p => MixedJointLevelData.mark_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k)) hmc
      (fun p q => (hC p ε q.1 q.2).2.2.2.1)⟩

local instance mixedNativeRandomRecursiveIdentity_inputSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeRandomRecursiveIdentity_inputBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeRandomRecursiveIdentity_bothSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeRandomRecursiveIdentity_bothBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ hsmall in
/-- Actual conditional physical first-defect identity for every genuine
finite recursive word and any finite history measure, with the entire
reference family determined by ORIGINAL random F_v states. Separate
positive time/heat cutoffs and the retained common-Haar mark remain. -/
theorem expected_level (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J) (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hP : P.coefficient=(fun z => κ+aV z)) (hbH : b≤H)
    (hwindow : (b:ℝ)-(v:ℝ)≤P.horizon)
    (ε : ℝ≥0) (hε : 0<(ε:ℝ)) (hgap : ∀ i,(ε:ℝ)≤(Z i).target-(b:ℝ)) (k : ℕ)
    (ν : Measure (CutoffWordHistories.History Unit k)) [IsFiniteMeasure ν]
    (A : Set Ω) (hA : MeasurableSet[𝓕 v] A) :
    (∫ q : CutoffWordHistories.History Unit k×Ω,Leaf (pastParameter q.2) ε k q.1 q.2 ∂ν.prod (μ.restrict A))=
      (∫ q : CutoffWordHistories.History Unit k×Ω,Ref (pastParameter q.2) ε k q.1 q.2 ∂ν.prod (μ.restrict A))+
      (∫ q : CutoffWordHistories.History Unit k×Ω,Loc (pastParameter q.2) ε k q.1 q.2 ∂ν.prod (μ.restrict A))+
      (∫ q : CutoffWordHistories.History Unit k×Ω,Mark (pastParameter q.2) ε k q.1 q.2 ∂ν.prod (μ.restrict A)) := by
  obtain ⟨hL,hR,hC,hM⟩ := pieces_integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε k ν A
  have hz := (MixedNativeRandomRecursiveStep.integrated_residual_on_past_event 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall J hIJ₀ hIJ₁ hnull hJ hlocal hΛ hP hbH hwindow ε hε hgap k ν A hA).2
  change (∫ q : CutoffWordHistories.History Unit k×Ω,Leaf (pastParameter q.2) ε k q.1 q.2-Ref (pastParameter q.2) ε k q.1 q.2-
    Loc (pastParameter q.2) ε k q.1 q.2-Mark (pastParameter q.2) ε k q.1 q.2 ∂ν.prod (μ.restrict A))=0 at hz
  have he₁ := integral_sub hL hR
  have he₂ := integral_sub (hL.sub hR) hC
  have he₃ := integral_sub ((hL.sub hR).sub hC) hM
  simp only [Pi.sub_apply] at he₁ he₂ he₃
  rw [he₃,he₂,he₁] at hz
  linarith only [hz]

end SHE.MixedNativeRandomRecursiveIdentity
