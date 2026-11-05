module

public import SHE.ControlledReferenceResidualContinuity
public import SHE.ControlledReferenceRemainderContinuity
public import SHE.PastParameterSectionExpectation

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false

namespace SHE.MixedNativeRandomReferenceStep
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
local instance mixedNativeRandomReferenceStep_circleSecondCountable : SecondCountableTopology StoppedFourier.CircleL2 :=
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
local notation "L" p => ControlledReferenceLevel.level P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF p

local notation "dU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U" => (dU).physicalState
local notation "V" => (dV).physicalState
local notation "XU" => (dU).physicalField
local notation "XV" => (dV).physicalField

variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

/-- The ORIGINAL actual states at the chosen past, without any
independent restart or new stochastic driver. -/
def randomParameter (ω : Ω) : Inputs :=
  (NativeHeatObservation.embed (S.first v ω),NativeHeatObservation.embed (S.second v ω-S.first v ω))

theorem randomParameter_stronglyMeasurable :
    StronglyMeasurable[𝓕 v] (randomParameter 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v) := by
  have hU : StronglyMeasurable[𝓕 v] (S.first v) :=
    (show IsStronglyPredictable 𝓕 S.first from S.first_predictable).stronglyAdapted v
  have hV : StronglyMeasurable[𝓕 v] (S.second v) :=
    (show IsStronglyPredictable 𝓕 S.second from S.second_predictable).stronglyAdapted v
  exact (NativeHeatObservation.embed.continuous.comp_stronglyMeasurable hU).prodMk
    (NativeHeatObservation.embed.continuous.comp_stronglyMeasurable (hV.sub hU))

local instance mixedNativeRandomReferenceStep_inputSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeRandomReferenceStep_inputBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeRandomReferenceStep_bothSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeRandomReferenceStep_bothBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ hsmall in
/-- Actual random-past-reference first-defect identity on EVERY F_v
event. The reference is the genuine canonical controlled TOTAL profile
based on U_v,V_v-U_v. Its applicability is derived by finite simple
past-parameter approximation and actual profile/covariance continuity,
rather than assumed as a random-reference Itô formula. The same original
full-H J and its ordinary block1 past locality are retained. -/
theorem residual_on_past_event (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J) (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hP : P.coefficient=(fun z => κ+aV z)) (hbH : b≤H)
    (hwindow : (b:ℝ)-(v:ℝ)≤P.horizon)
    {δ : ℝ} (hδ : 0<δ) (hgap : ∀ i,δ≤(Z i).target-(b:ℝ))
    (A : Set Ω) (hA : MeasurableSet[𝓕 v] A) :
    Integrable (fun ω => ControlledReferenceResidual.residual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF
      (randomParameter 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω) ω) (μ.restrict A) ∧
    (∫ ω in A,ControlledReferenceResidual.residual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF
      (randomParameter 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω) ω ∂μ)=0 := by
  let K := ControlledReferenceResidual.residual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF
  obtain ⟨C,hC,hCb⟩ := ControlledReferenceResidualBounds.uniform_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hΛ
  have hz : ∀ p B,MeasurableSet[𝓕 v] B → (∫ ω in B,K p ω ∂μ.restrict A)=0 := by
    intro p B hB
    rw [Measure.restrict_restrict (𝓕.le v B hB)]
    exact (ControlledReferenceResidual.residual_on_past_event 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF J hIJ₀ hIJ₁ hnull hJ hlocal hΛ hbH hδ hgap p (B∩A) (hB.inter hA)).2
  exact PastParameterSectionExpectation.integral_random_eq_zero (𝓕 v) (𝓕.le v) (μ.restrict A) K
    (ControlledReferenceResidual.residual_section_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF)
    (fun _ => C) (integrable_const C) hCb hz
    (randomParameter_stronglyMeasurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v)
    (ControlledReferenceResidualContinuity.continuous_residual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hsmall hΛ)

end SHE.MixedNativeRandomReferenceStep

