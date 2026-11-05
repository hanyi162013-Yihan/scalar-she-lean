module

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

namespace SHE.ControlledReferenceFamilyMark
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

open CutoffWordHistories UncutWordEvaluation
local notation "NL" => (fun p k => normalizedLevel (Base p) k)
local notation "Mmark" => MixedJointLevelData.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "UM" => (fun p k h ω => MixedJointUncutMark.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p) k h ω)
local notation "R₀" => ControlledReferenceLevel.referenceData P (fun z => κ+aV z) hAs Λ θ v b hvb (0,0)

theorem normalized_mark_bound (hΛ : 0≤Λ) (k : ℕ) : ∃ K : ℝ,0≤K ∧ ∀ (p : Inputs) (h : History X k) ω,
    ‖Mmark (NL p k) h ω‖≤K := by
  have hJ := ControlledReferenceFamilyBounds.normalized_uniform P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF hFm k
  obtain ⟨C,hCn,hC⟩ := hJ.norm_bound
  obtain ⟨D,hDn,hD⟩ := hJ.fderiv.norm_bound
  obtain ⟨B,hBn,hB⟩ := hJ.fderiv.fderiv.norm_bound
  have hM : 0≤M := hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  let K := (((n+k:ℕ):ℝ)^2*M*B)*PhysicalRemainderMass.heatMass (b:ℝ)
  have hKn : 0≤K := mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hM) hBn)
    (PhysicalRemainderMass.heatMass_nonneg b.2)
  refine ⟨K,hKn,fun p h ω => ?_⟩
  let E := MixedJointLevelData.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (NL p k)
  let I := JointWordDefect.integrand (NL p k) Λ U V XU XV E
  let T := (NL p k).terminal h
  have hvT : (v:ℝ)≤T := (NL p k).terminal_base h
  have hH (q : (History X k×Ω)×ℝ) : ‖JointWordHessian.field (NL p k) Λ U V XU XV q‖≤B :=
    BackwardRegularity.gaussian_state_hessian_bound _ (((NL p k).test_uniform.smooth q.1.1).of_le (by simp))
      (hC (p,q.1.1)) (hD (p,q.1.1)) (hB (p,q.1.1)) _
  have hb (t : ℝ) (ht : t∈Ioo (v:ℝ) T) :
      ‖I ((h,ω),t)‖≤(((n+k:ℕ):ℝ)^2*M*B)*(1+StoppedFourier.heatConstant*(T-t)^(-(1/2:ℝ))) :=
    JointWordDefect.integrand_bound (NL p k) Λ hM hBn hH
      (fun q ω t ht => MixedJointLevelData.defect_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        (NL p k) hΛ q ω ht) h ω ht
  have hi := CovarianceEndpoint.endpoint_majorant_integrable (q := (v:ℝ)) (s := T) (((n+k:ℕ):ℝ)^2*M*B)
  have hd : ∀ᵐ t∂volume,t∈Ioc (v:ℝ) T → ‖I ((h,ω),t)‖≤
      (((n+k:ℕ):ℝ)^2*M*B)*(1+StoppedFourier.heatConstant*(T-t)^(-(1/2:ℝ))) := by
    filter_upwards [volume.ae_ne T] with t hne ht
    exact hb t ⟨ht.1,lt_of_le_of_ne ht.2 hne⟩
  have hh := intervalIntegral.norm_integral_le_of_norm_le hvT hd hi
  rw [intervalIntegral.integral_const_mul,PhysicalRemainderMass.heat_majorant_mass hvT] at hh
  have hTb : T≤(b:ℝ) := (NL p k).terminal_horizon h
  exact hh.trans (mul_le_mul_of_nonneg_left
    (PhysicalRemainderMass.heatMass_mono (sub_nonneg.mpr hvT)
      (by linarith [v.2] : T-(v:ℝ)≤b)) (by positivity))

theorem mark_bound (hΛ : 0≤Λ) (k : ℕ) : ∃ K : ℝ,0≤K ∧ ∀ (p : Inputs) (h : History X k) ω,
    ‖UM p k h ω‖≤K*UncutSmoothWords.weight (Base (0,0)) k h := by
  obtain ⟨K,hKn,hK⟩ := normalized_mark_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hΛ k
  refine ⟨K,hKn,fun p h ω => ?_⟩
  change ‖UncutSmoothWords.weight (Base p) k h*Mmark (NL p k) h ω‖≤_
  rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (UncutSmoothWords.weight_nonneg (Base p) k h)]
  have hh := mul_le_mul_of_nonneg_left (hK p h ω) (UncutSmoothWords.weight_nonneg (Base p) k h)
  rw [ControlledReferenceFamilyBounds.weight_eq P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF hFm p (0,0) k h] at hh
  rw [ControlledReferenceFamilyBounds.weight_eq P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF hFm p (0,0) k h]
  exact hh.trans_eq (mul_comm _ _)

theorem terminal_eq (p p' : Inputs) (k : ℕ) (h : History X k) :
    (NL p k).terminal h=(NL p' k).terminal h :=
  ControlledReferenceFamilyBounds.carrier_terminal_eq P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF hFm p p' k h

theorem defect_eq (p p' : Inputs) (k : ℕ) :
    MixedJointLevelData.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (NL p k)=
      MixedJointLevelData.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (NL p' k) := by
  funext q
  unfold MixedJointLevelData.defect
  change MixedNativeJointBracketDefect.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    ((CutoffCarriers.carrier (Base p) k).observations.observations q.1.1) (q.2.toNNReal,q.1.2)=_
  rw [ControlledReferenceFamilyBounds.carrier_observations_eq P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF hFm p p' k q.1.1]
  rfl
include hsmall in
/-- Continuity of the literal retained common-Haar defect mark for
genuinely moving recursive tests and random-reference parameters. -/
theorem normalized_mark_continuous (hΛ : 0≤Λ) (k : ℕ) (h : History X k) (ω : Ω) :
    Continuous (fun p : Inputs => MixedJointLevelData.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (NL p k) h ω) := by
  have hJ := ControlledReferenceFamilyBounds.normalized_uniform P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF hFm k
  obtain ⟨C,hCn,hC⟩ := hJ.norm_bound
  obtain ⟨D,hDn,hD⟩ := hJ.fderiv.norm_bound
  obtain ⟨B,hBn,hB⟩ := hJ.fderiv.fderiv.norm_bound
  have hM : 0≤M := hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  let T := (NL (0,0) k).terminal h
  let E := fun p : Inputs => MixedJointLevelData.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (NL p k)
  let I := fun p : Inputs => JointWordDefect.integrand (NL p k) Λ U V XU XV (E p)
  have hHb (p : Inputs) (q : (History X k×Ω)×ℝ) :
      ‖JointWordHessian.field (NL p k) Λ U V XU XV q‖≤B :=
    BackwardRegularity.gaussian_state_hessian_bound _ (((NL p k).test_uniform.smooth q.1.1).of_le (by simp))
      (hC (p,q.1.1)) (hD (p,q.1.1)) (hB (p,q.1.1)) _
  have hvT : (v:ℝ)≤T := (NL (0,0) k).terminal_base h
  have he : (fun p : Inputs => MixedJointLevelData.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (NL p k) h ω)=
      fun p => ∫ t,I p ((h,ω),t) ∂volume.restrict (Ioc (v:ℝ) T) := by
    funext p
    unfold MixedJointLevelData.mark JointWordDefect.mark
    rw [terminal_eq (Λ:=Λ) (κ:=κ) (P:=P) (hAs:=hAs) (θ:=θ) (v:=v) (b:=b) (hvb:=hvb) (Z:=Z) (htarget:=htarget) (hstop:=hstop) (F:=F) (hF:=hF) (hFm:=hFm) p (0,0) k h]
    exact intervalIntegral.integral_of_le hvT
  rw [he]
  apply continuous_of_dominated (bound := fun t : ℝ => (((n+k:ℕ):ℝ)^2*M*B)*(1+heatConstant*(T-t)^(-(1/2:ℝ))))
  · intro p
    have hm := JointWordDefect.integrand_measurable (NL p k) Λ
      (dU).physicalState_measurable (dV).physicalState_measurable
      (dU).physicalField_measurable (dV).physicalField_measurable
      (MixedJointLevelData.defect_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (NL p k))
    have hh := hm.comp ((measurable_const (a := (h,ω))).prodMk measurable_id)
    exact hh.aestronglyMeasurable
  · intro p
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne T)] with t ht hne
    have hpT : (NL p k).terminal h=T :=
      terminal_eq (Λ:=Λ) (κ:=κ) (P:=P) (hAs:=hAs) (θ:=θ) (v:=v) (b:=b) (hvb:=hvb) (Z:=Z) (htarget:=htarget) (hstop:=hstop) (F:=F) (hF:=hF) (hFm:=hFm) p (0,0) k h
    have ht' : t∈Ioo (v:ℝ) ((NL p k).terminal h) := by
      rw [hpT]
      exact ⟨ht.1,lt_of_le_of_ne ht.2 hne⟩
    have hh := JointWordDefect.integrand_bound (NL p k) Λ hM hBn (hHb p)
      (fun q ω t ht => MixedJointLevelData.defect_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        (NL p k) hΛ q ω ht) h ω ht'
    simpa only [hpT] using hh
  · exact (CovarianceEndpoint.endpoint_majorant_integrable (q := (v:ℝ)) (s := T) (((n+k:ℕ):ℝ)^2*M*B)).1
  · apply Filter.Eventually.of_forall
    intro t
    have hH := ControlledReferenceFamilyBackward.hessian_field_continuous P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF hFm hsmall
      U V XU XV hΛ k h ω t
    have hE : ∀ p : Inputs,E p=E (0,0) := fun p =>
      defect_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF hFm p (0,0) k
    have heq : (fun p : Inputs => I p ((h,ω),t))=
        fun p : Inputs => (1/2:ℝ)*GaussianTaylorAverage.covarianceAction (E (0,0) ((h,ω),t))
          (JointWordHessian.field (NL p k) Λ U V XU XV ((h,ω),t)) := by
      funext p
      dsimp only [I,JointWordDefect.integrand]
      rw [hE p]
    rw [heq]
    apply Continuous.const_mul
    unfold GaussianTaylorAverage.covarianceAction
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    exact continuous_const.mul ((hH.clm_apply continuous_const).clm_apply continuous_const)

include hsmall in
theorem mark_parameter_continuous (hΛ : 0≤Λ) (k : ℕ) (h : History X k) (ω : Ω) :
    Continuous (fun p : Inputs => UM p k h ω) := by
  have hh := (normalized_mark_continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hΛ k h ω).const_mul (UncutSmoothWords.weight (Base (0,0)) k h)
  convert hh using 1
  funext p
  change UncutSmoothWords.weight (Base p) k h*Mmark (NL p k) h ω=_
  rw [ControlledReferenceFamilyBounds.weight_eq P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF hFm p (0,0) k h]

include hsmall in
theorem diagonal_measurable (hΛ : 0≤Λ) (u : Ω→Inputs) (hu : StronglyMeasurable u) (k : ℕ) :
    Measurable (fun q : History X k×Ω => UM (u q.2) k q.1 q.2) := by
  let Q := History X k×Ω
  have huQ : StronglyMeasurable (fun q : Q => u q.2) := hu.comp_measurable measurable_snd
  have hm (p : Inputs) : Measurable (fun q : Q => UM p k q.1 q.2) :=
    MixedJointUncutMark.mark_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p) k
  have hh := PastParameterDiagonal.stronglyMeasurable_diagonal (inferInstance : MeasurableSpace Q) le_rfl
    (fun p q => UM p k q.1 q.2) hm huQ
    (fun q => mark_parameter_continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hΛ k q.1 q.2)
  exact hh.measurable

end SHE.ControlledReferenceFamilyMark
