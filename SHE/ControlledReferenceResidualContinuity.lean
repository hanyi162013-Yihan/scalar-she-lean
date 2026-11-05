module

public import SHE.ControlledReferenceResidualBounds
public import SHE.ControlledReferenceRemainderContinuity
public import SHE.PastParameterSectionExpectation

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false

namespace SHE.ControlledReferenceResidualContinuity
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
local notation "L" p => ControlledReferenceLevel.level P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF p

local notation "dU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U" => (dU).physicalState
local notation "V" => (dV).physicalState
local notation "XU" => (dU).physicalField
local notation "XV" => (dV).physicalField

variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

include hsmall in
theorem continuous_hessian (hΛ : 0≤Λ) (ω : Ω) (t : ℝ) :
    Continuous (fun p : Inputs => JointWordHessian.field (L p) Λ U V XU XV (((),ω),t)) := by
  let y := JointWordAnalytic.state (L (0,0)) Λ U V XU XV () ω t
  have hh := (ControlledReferenceCovariance.hessian_inputs_continuous P hΛ θ v hsmall Z b htarget
    (by exact_mod_cast hvb) hF t).comp (continuous_id.prodMk (continuous_const (y := y)))
  convert hh using 1
  funext p
  rfl

include hsmall in
theorem continuous_reference (hΛ : 0≤Λ) (ω : Ω) :
    Continuous (fun p : Inputs => MixedJointLevelData.reference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p) () ω) := by
  let y := JointWordAnalytic.state (L (0,0)) Λ U V XU XV () ω v
  have hh := (ControlledReferenceCovariance.backward_inputs_continuous P hΛ θ v hsmall Z b htarget
    (by exact_mod_cast hvb) hF v).comp (continuous_id.prodMk (continuous_const (y := y)))
  convert hh using 1
  funext p
  rfl

include hsmall in
theorem continuous_mark (hΛ : 0≤Λ) (ω : Ω) :
    Continuous (fun p : Inputs => MixedJointLevelData.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p) () ω) := by
  obtain ⟨C,hC⟩ := hF.norm_bound
  obtain ⟨D,hD⟩ := hF.fderiv.norm_bound
  obtain ⟨B,hB⟩ := hF.fderiv.fderiv.norm_bound
  have hBn : 0≤B := (norm_nonneg _).trans (hB 0)
  have hM : 0≤M := hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  let E := MixedJointLevelData.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L (0,0))
  let I := fun p : Inputs => JointWordDefect.integrand (L p) Λ U V XU XV E
  have hHb (p : Inputs) (q : (Unit×Ω)×ℝ) : ‖JointWordHessian.field (L p) Λ U V XU XV q‖≤B :=
    BackwardRegularity.gaussian_state_hessian_bound _ (hF.smooth.of_le (by simp)) hC hD hB _
  have hvb' : (v:ℝ)≤(b:ℝ) := by exact_mod_cast hvb
  have he : (fun p : Inputs => MixedJointLevelData.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p) () ω)=
      fun p => ∫ t,I p (((),ω),t) ∂volume.restrict (Ioc (v:ℝ) (b:ℝ)) := by
    funext p
    exact intervalIntegral.integral_of_le hvb'
  rw [he]
  apply continuous_of_dominated (bound := fun t : ℝ => ((n:ℝ)^2*M*B)*(1+heatConstant*((b:ℝ)-t)^(-(1/2:ℝ))))
  · intro p
    have hm := JointWordDefect.integrand_measurable (L p) Λ
      (dU).physicalState_measurable (dV).physicalState_measurable
      (dU).physicalField_measurable (dV).physicalField_measurable
      (MixedJointLevelData.defect_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L (0,0)))
    exact (hm.comp ((measurable_const (a := ((),ω))).prodMk measurable_id)).aestronglyMeasurable
  · intro p
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne (b:ℝ))] with t ht hne
    exact JointWordDefect.integrand_bound (L p) Λ hM hBn (hHb p)
      (fun q ω t ht => MixedJointLevelData.defect_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        (L (0,0)) hΛ q ω ht) () ω ⟨ht.1,lt_of_le_of_ne ht.2 hne⟩
  · exact (CovarianceEndpoint.endpoint_majorant_integrable (q := (v:ℝ)) (s := (b:ℝ)) ((n:ℝ)^2*M*B)).1
  · apply Filter.Eventually.of_forall
    intro t
    have hH := continuous_hessian 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hsmall hΛ ω t
    apply Continuous.const_mul
    unfold GaussianTaylorAverage.covarianceAction
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    exact continuous_const.mul ((hH.clm_apply continuous_const).clm_apply continuous_const)

include hsmall in
/-- The full actual first-defect residual is continuous in the two
reference inputs, including singular Gaussian covariance and collisions. -/
theorem continuous_residual (hΛ : 0≤Λ) (ω : Ω) :
    Continuous (fun p : Inputs => ControlledReferenceResidual.residual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF p ω) := by
  have hl : Continuous (fun p : Inputs => MixedJointLevelData.leaf 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p) () ω) := by
    convert (continuous_const (y := MixedJointLevelData.leaf 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L (0,0)) () ω)) using 1
    funext p
    rfl
  have hr := continuous_reference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF hsmall hΛ ω
  have hc := ControlledReferenceRemainderContinuity.continuous_remainder P (fun z => κ+aV z) hAs hΛ θ v b hvb Z htarget hstop F hF hsmall
    U V XU XV (dU).physicalState_measurable (dV).physicalState_measurable
    (dU).physicalField_measurable (dV).physicalField_measurable ω
  have hm := continuous_mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF hsmall hΛ ω
  exact ((hl.sub hr).sub hc).sub hm

end SHE.ControlledReferenceResidualContinuity

