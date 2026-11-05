module

public import SHE.ControlledReferenceRecursiveResidualBounds
public import SHE.ControlledReferenceRecursiveRemainder
public import SHE.ControlledReferenceRecursiveFields
public import SHE.ControlledReferenceRemainderContinuity
public import SHE.PastParameterSectionExpectation

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false

namespace SHE.ControlledReferenceRecursiveResidualContinuity
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

theorem defect_eq (p p' : Inputs) (ε : ℝ≥0) (k : ℕ) :
    MixedJointLevelData.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k)=
      MixedJointLevelData.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p' ε k) := by
  funext q
  unfold MixedJointLevelData.defect
  rw [ControlledReferenceRecursiveBounds.observations_eq P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF δ hδ p p' ε k q.1.1]

include hsmall in
/-- Continuity of the literal retained common-Haar defect mark for
genuinely moving recursive tests and random-reference parameters. -/
theorem continuous_mark (hΛ : 0≤Λ) (ε : ℝ≥0) (k : ℕ) (h : CutoffWordHistories.History Unit k) (ω : Ω) :
    Continuous (fun p : Inputs => MixedJointLevelData.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k) h ω) := by
  have hJ := ControlledReferenceRecursiveBounds.test_uniform P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF δ hδ k
  obtain ⟨C,hCn,hC⟩ := hJ.norm_bound
  obtain ⟨D,hDn,hD⟩ := hJ.fderiv.norm_bound
  obtain ⟨B,hBn,hB⟩ := hJ.fderiv.fderiv.norm_bound
  have hM : 0≤M := hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  let T := (L (0,0) ε k).terminal h
  let E := fun p : Inputs => MixedJointLevelData.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k)
  let I := fun p : Inputs => JointWordDefect.integrand (L p ε k) Λ U V XU XV (E p)
  have hHb (p : Inputs) (q : (CutoffWordHistories.History Unit k×Ω)×ℝ) :
      ‖JointWordHessian.field (L p ε k) Λ U V XU XV q‖≤B :=
    BackwardRegularity.gaussian_state_hessian_bound _ (((L p ε k).test_uniform.smooth q.1.1).of_le (by simp))
      (hC (p,(ε,q.1.1))) (hD (p,(ε,q.1.1))) (hB (p,(ε,q.1.1))) _
  have hvT : (v:ℝ)≤T := (L (0,0) ε k).terminal_base h
  have he : (fun p : Inputs => MixedJointLevelData.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k) h ω)=
      fun p => ∫ t,I p ((h,ω),t) ∂volume.restrict (Ioc (v:ℝ) T) := by
    funext p
    unfold MixedJointLevelData.mark JointWordDefect.mark
    rw [ControlledReferenceRecursiveBounds.terminal_eq P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF δ hδ p (0,0) ε ε k h]
    exact intervalIntegral.integral_of_le hvT
  rw [he]
  apply continuous_of_dominated (bound := fun t : ℝ => (((n+k:ℕ):ℝ)^2*M*B)*(1+heatConstant*(T-t)^(-(1/2:ℝ))))
  · intro p
    have hm := JointWordDefect.integrand_measurable (L p ε k) Λ
      (dU).physicalState_measurable (dV).physicalState_measurable
      (dU).physicalField_measurable (dV).physicalField_measurable
      (MixedJointLevelData.defect_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k))
    have hh := hm.comp ((measurable_const (a := (h,ω))).prodMk measurable_id)
    exact hh.aestronglyMeasurable
  · intro p
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne T)] with t ht hne
    have hpT : (L p ε k).terminal h=T :=
      ControlledReferenceRecursiveBounds.terminal_eq P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF δ hδ p (0,0) ε ε k h
    have ht' : t∈Ioo (v:ℝ) ((L p ε k).terminal h) := by
      rw [hpT]
      exact ⟨ht.1,lt_of_le_of_ne ht.2 hne⟩
    have hh := JointWordDefect.integrand_bound (L p ε k) Λ hM hBn (hHb p)
      (fun q ω t ht => MixedJointLevelData.defect_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        (L p ε k) hΛ q ω ht) h ω ht'
    simpa only [hpT] using hh
  · exact (CovarianceEndpoint.endpoint_majorant_integrable (q := (v:ℝ)) (s := T) (((n+k:ℕ):ℝ)^2*M*B)).1
  · apply Filter.Eventually.of_forall
    intro t
    have hH := ControlledReferenceRecursiveFields.continuous_hessian P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall
      U V XU XV hΛ ε k h ω t
    have hE : ∀ p : Inputs,E p=E (0,0) := fun p =>
      defect_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF δ hδ p (0,0) ε k
    have heq : (fun p : Inputs => I p ((h,ω),t))=
        fun p : Inputs => (1/2:ℝ)*GaussianTaylorAverage.covarianceAction (E (0,0) ((h,ω),t))
          (JointWordHessian.field (L p ε k) Λ U V XU XV ((h,ω),t)) := by
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
/-- The actual finite-depth first-defect residual is continuous in
both original past inputs, with the test and Gaussian reference changing
at EVERY recursive insertion. -/
theorem continuous_residual (hΛ : 0≤Λ) (ε : ℝ≥0) (k : ℕ) (h : CutoffWordHistories.History Unit k) (ω : Ω) :
    Continuous (fun p : Inputs => MixedJointPastExpectedLevel.noiseVersion 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k) h ω) := by
  have hl := ControlledReferenceRecursiveFields.continuous_leaf P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall
    U V XU XV hΛ ε k h ω
  have hr := ControlledReferenceRecursiveFields.continuous_reference P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall
    U V XU XV hΛ ε k h ω
  have hc := ControlledReferenceRecursiveRemainder.continuous_remainder P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall
    U V XU XV (dU).physicalState_measurable (dV).physicalState_measurable
    (dU).physicalField_measurable (dV).physicalField_measurable hΛ ε k h ω
  have hm := continuous_mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε k h ω
  exact ((hl.sub hr).sub hc).sub hm

end SHE.ControlledReferenceRecursiveResidualContinuity
