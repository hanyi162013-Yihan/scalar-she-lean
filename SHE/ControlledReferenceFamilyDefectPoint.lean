module

public import SHE.MixedJointUncutDefectTrace
public import SHE.ControlledReferenceFamilyMark
public import SHE.MixedNativeRandomRecursiveIdentity
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

namespace SHE.ControlledReferenceFamilyDefectPoint
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
local instance controlledReferenceFamilyMark_circleSecondCountable : SecondCountableTopology StoppedFourier.CircleL2 :=
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

open CutoffWordHistories UncutWordEvaluation CutoffCarriers
local notation "NL" => (fun p k => normalizedLevel (Base p) k)
local notation "Mmark" => MixedJointLevelData.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "UM" => (fun p k h ω => MixedJointUncutMark.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p) k h ω)
local notation "R₀" => ControlledReferenceLevel.referenceData P (fun z => κ+aV z) hAs Λ θ v b hvb (0,0)


/-- Coarse joint-time domination, uniform in both actual past states.
Its smooth-depth constant is used only to justify Fubini. -/
theorem point_bound (hΛ:0≤Λ)(k:ℕ):∃C:ℝ,0≤C ∧ ∀(p:Inputs)(h:History X k) ω q,
    q∈Ioo (v:ℝ) ((carrier (Base p) k).terminal h) →
    ‖MixedJointUncutDefectTrace.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (Base p) k h ω q‖≤
      C*UncutSmoothWords.weight (Base (0,0)) k h*
        (1+heatConstant*(((carrier (Base (0,0)) k).terminal h)-q)^(-(1/2:ℝ))) :=by
  have hJ:=ControlledReferenceFamilyBounds.normalized_uniform P (fun z=>κ+aV z) hAs Λ θ v b hvb
    Z htarget hstop F hF hFm k
  obtain ⟨C,hCn,hC⟩:=hJ.norm_bound
  obtain ⟨D,hDn,hD⟩:=hJ.fderiv.norm_bound
  obtain ⟨B,hBn,hB⟩:=hJ.fderiv.fderiv.norm_bound
  have hM:0≤M:=hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  refine ⟨((n+k:ℕ):ℝ)^2*M*B,by positivity,?_⟩
  intro p h ω q hq
  have hH (z:(History X k×Ω)×ℝ):‖JointWordHessian.field (NL p k) Λ U V XU XV z‖≤B:=
    BackwardRegularity.gaussian_state_hessian_bound _ (((NL p k).test_uniform.smooth z.1.1).of_le (by simp))
      (hC (p,z.1.1)) (hD (p,z.1.1)) (hB (p,z.1.1)) _
  have hb:=JointWordDefect.integrand_bound (NL p k) Λ hM hBn hH
    (fun h ω q hq=>MixedJointLevelData.defect_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S (NL p k) hΛ h ω hq) h ω hq
  rw [MixedJointUncutDefectTrace.point_eq_weight 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S (Base p) k h ω q ⟨hq.1.le,hq.2.le⟩,norm_mul,
    Real.norm_of_nonneg (UncutSmoothWords.weight_nonneg (Base p) k h)]
  have hh:=mul_le_mul_of_nonneg_left hb (UncutSmoothWords.weight_nonneg (Base p) k h)
  rw [ControlledReferenceFamilyBounds.weight_eq P (fun z=>κ+aV z) hAs Λ θ v b hvb Z htarget hstop
    F hF hFm p (0,0) k h] at hh
  have hT:=ControlledReferenceFamilyBounds.carrier_terminal_eq P (fun z=>κ+aV z) hAs Λ θ v b hvb
    Z htarget hstop F hF hFm p (0,0) k h
  change (carrier (Base p) k).terminal h=_ at hT
  change _≤UncutSmoothWords.weight (Base (0,0)) k h*
    (((n+k:ℕ):ℝ)^2*M*B*(1+heatConstant*((carrier (Base p) k).terminal h-q)^(-(1/2:ℝ)))) at hh
  rw [hT] at hh
  rw [ControlledReferenceFamilyBounds.weight_eq P (fun z=>κ+aV z) hAs Λ θ v b hvb
    Z htarget hstop F hF hFm p (0,0) k h]
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hh

include hsmall in
/-- Moving-family active points have a Borel actual random-past
substitution, rather than a fixed-level measurability assumption. -/
theorem diagonal_measurable (hΛ:0≤Λ)(u:Ω→Inputs)(hu:StronglyMeasurable u)(k:ℕ):
    Measurable (fun z:(History X k×Ω)×ℝ=>MixedJointUncutDefectTrace.activePoint
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base (u z.1.2)) k z):=by
  let Q:=(History X k×Ω)×ℝ
  let A:=fun (p:Inputs)(z:Q)=>MixedJointUncutDefectTrace.activePoint
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p) k z
  have hm (p:Inputs):Measurable (A p):=
    MixedJointUncutDefectTrace.activePoint_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S (Base p) k
  have hc (z:Q):Continuous (fun p:Inputs=>A p z):=by
    let T:=(carrier (Base (0,0)) k).terminal z.1.1
    have he (p:Inputs):A p z=if (v:ℝ)≤z.2 ∧ z.2≤T then
        UncutSmoothWords.weight (Base (0,0)) k z.1.1*
        JointWordDefect.integrand (NL p k) Λ U V XU XV
          (MixedJointLevelData.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
            (NL (0,0) k)) z else 0:=by
      have hT:=ControlledReferenceFamilyBounds.carrier_terminal_eq P (fun z=>κ+aV z) hAs Λ θ v b hvb
        Z htarget hstop F hF hFm p (0,0) k z.1.1
      change (carrier (Base p) k).terminal z.1.1=T at hT
      dsimp only [A,MixedJointUncutDefectTrace.activePoint]
      change (if (v:ℝ)≤z.2 ∧ z.2≤(carrier (Base p) k).terminal z.1.1 then _ else 0)=_
      rw [hT]
      split_ifs with hz
      · rw [MixedJointUncutDefectTrace.point_eq_weight 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
          I₀ I₁ u₀ v₀ S (Base p) k z.1.1 z.1.2 z.2 (by exact ⟨hz.1,hT.symm ▸ hz.2⟩)]
        rw [ControlledReferenceFamilyBounds.weight_eq P (fun z=>κ+aV z) hAs Λ θ v b hvb
          Z htarget hstop F hF hFm p (0,0) k z.1.1]
        rw [ControlledReferenceFamilyMark.defect_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
          P hAs θ v b hvb Z htarget hstop F hF hFm p (0,0) k]
      · rfl
    simp_rw [he]
    by_cases hz:(v:ℝ)≤z.2 ∧ z.2≤T
    · simp only [if_pos hz]
      apply Continuous.const_mul
      unfold JointWordDefect.integrand GaussianTaylorAverage.covarianceAction
      apply Continuous.const_mul
      apply continuous_finsetSum
      intro i _
      apply continuous_finsetSum
      intro j _
      exact continuous_const.mul (((ControlledReferenceFamilyBackward.hessian_field_continuous
        P (fun z=>κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF hFm hsmall
        U V XU XV hΛ k z.1.1 z.1.2 z.2).clm_apply continuous_const).clm_apply continuous_const)
    · simp only [if_neg hz]
      exact continuous_const
  exact (PastParameterDiagonal.stronglyMeasurable_diagonal (inferInstance:MeasurableSpace Q) le_rfl
    A hm (hu.comp_measurable measurable_fst.snd) hc).measurable

end SHE.ControlledReferenceFamilyDefectPoint
