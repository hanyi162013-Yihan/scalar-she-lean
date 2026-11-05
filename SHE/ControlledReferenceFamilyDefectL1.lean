module

public import SHE.ControlledReferenceFamilyDefectPoint
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

namespace SHE.ControlledReferenceFamilyDefectL1
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



local notation "AP"=>fun (k:ℕ)(p:Inputs)(h:History X k)(ω:Ω)(q:ℝ)=>
  MixedJointUncutDefectTrace.activePoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    (Base p) k ((h,ω),q)

/-- Full current-time L1 mass, with every original old-history weight
and a constant uniform in both past inputs. Endpoint values are removed
only on their actual Lebesgue-null sets. -/
theorem active_mass (hΛ:0≤Λ)(k:ℕ):∃K:ℝ,0≤K ∧∀(p:Inputs)(h:History X k) ω,
    Integrable (AP k p h ω) volume ∧
      (∫q,‖AP k p h ω q‖)≤K*UncutSmoothWords.weight (Base (0,0)) k h:=by
  obtain ⟨C,hCn,hC⟩:=ControlledReferenceFamilyDefectPoint.point_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF hFm hΛ k
  refine ⟨C*PhysicalRemainderMass.heatMass b,mul_nonneg hCn
    (PhysicalRemainderMass.heatMass_nonneg b.2),?_⟩
  intro p h ω
  let T:=(carrier (Base (0,0)) k).terminal h
  let W:=UncutSmoothWords.weight (Base (0,0)) k h
  let g:ℝ→ℝ:=(Ioc (v:ℝ) T).indicator
    (fun q=>C*W*(1+heatConstant*(T-q)^(-(1/2:ℝ))))
  have hvT:(v:ℝ)≤T:=(carrier (Base (0,0)) k).terminal_base h
  have hTb:T≤(b:ℝ):=(carrier (Base (0,0)) k).terminal_horizon h
  have hW:0≤W:=UncutSmoothWords.weight_nonneg (Base (0,0)) k h
  have hpT:(carrier (Base p) k).terminal h=T:=
    ControlledReferenceFamilyBounds.carrier_terminal_eq P (fun z=>κ+aV z) hAs Λ θ v b hvb
      Z htarget hstop F hF hFm p (0,0) k h
  have hgi:Integrable g volume:=by
    apply (integrable_indicator_iff measurableSet_Ioc).mpr
    simpa only [uIoc_of_le hvT] using
      (CovarianceEndpoint.endpoint_majorant_integrable (q:=(v:ℝ)) (s:=T) (C*W)).1
  have hdom:∀ᵐq∂volume,‖AP k p h ω q‖≤g q:=by
    filter_upwards [volume.ae_ne (v:ℝ),volume.ae_ne T] with q hqv hqT
    by_cases hz:(v:ℝ)≤q ∧ q≤T
    · have hqo:q∈Ioo (v:ℝ) T:=⟨lt_of_le_of_ne hz.1 hqv.symm,lt_of_le_of_ne hz.2 hqT⟩
      have he:AP k p h ω q=MixedJointUncutDefectTrace.point
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p) k h ω q:=by
        change (if (v:ℝ)≤q ∧ q≤(carrier (Base p) k).terminal h then _ else 0)=_
        rw [hpT,if_pos hz]
      dsimp only at he
      rw [he]
      have hqg:q∈Ioc (v:ℝ) T:=⟨hqo.1,hz.2⟩
      rw [show g q=C*W*(1+heatConstant*(T-q)^(-(1/2:ℝ))) from Set.indicator_of_mem hqg _]
      exact hC p h ω q ⟨hqo.1,by simpa only [hpT] using hqo.2⟩
    · have he:AP k p h ω q=0:=by
        change (if (v:ℝ)≤q ∧ q≤(carrier (Base p) k).terminal h then _ else 0)=_
        rw [hpT,if_neg hz]
      dsimp only at he
      rw [he,norm_zero]
      exact Set.indicator_nonneg (fun r hr=>mul_nonneg (mul_nonneg hCn hW)
        (add_nonneg zero_le_one (mul_nonneg heatConstant_pos.le
          (Real.rpow_nonneg (sub_nonneg.mpr hr.2) _)))) q
  have hm:Measurable (AP k p h ω):=
    (MixedJointUncutDefectTrace.activePoint_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p) k).comp
        (measurable_const.prodMk measurable_id)
  have hi:Integrable (AP k p h ω) volume:=hgi.mono' hm.aestronglyMeasurable hdom
  refine ⟨hi,(integral_mono_ae hi.norm hgi hdom).trans ?_⟩
  have hg:(∫q,g q)=C*W*PhysicalRemainderMass.heatMass (T-v):=by
    change (∫q,(Ioc (v:ℝ) T).indicator
      (fun q=>C*W*(1+heatConstant*(T-q)^(-(1/2:ℝ)))) q)=_
    rw [integral_indicator measurableSet_Ioc,←intervalIntegral.integral_of_le hvT,
      intervalIntegral.integral_const_mul,PhysicalRemainderMass.heat_majorant_mass hvT]
    rfl
  rw [hg]
  have hmass:=PhysicalRemainderMass.heatMass_mono (sub_nonneg.mpr hvT)
    (by linarith [v.2]:T-(v:ℝ)≤b)
  exact (mul_le_mul_of_nonneg_left hmass (mul_nonneg hCn hW)).trans_eq (by ring)

/-- The same complete history/current-time L1 statement holds for
each fixed original sample and each actual past input. -/
theorem history_integrable (hΛ:0≤Λ)(ξ:Measure X)[IsFiniteMeasure ξ](k:ℕ)(p:Inputs)(ω:Ω):
    Integrable (fun z:History X k×ℝ=>AP k p z.1 ω z.2)
      ((historyMeasure R₀ ξ k).prod volume):=by
  have hm:Measurable (fun z:History X k×ℝ=>AP k p z.1 ω z.2):=
    (MixedJointUncutDefectTrace.activePoint_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p) k).comp
        ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
  obtain ⟨K,hKn,hK⟩:=active_mass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hΛ k
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun h=>(hK p h ω).1),?_⟩
  apply ((UncutHistoryMass.weight_integrable (Base (0,0)) ξ k).const_mul K).mono'
    hm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  filter_upwards with h
  rw [Real.norm_of_nonneg (integral_nonneg (fun _=>norm_nonneg _))]
  exact (hK p h ω).2

include hsmall in
/-- Joint old-history/sample/current-time integrability for the actual
moving past input. It is proved before swapping the space/time integrals;
no square is moved inside the current-time integral. -/
theorem joint_integrable (hΛ:0≤Λ)(u:Ω→Inputs)(hu:StronglyMeasurable u)
    (ξ:Measure X)[IsFiniteMeasure ξ](k:ℕ):
    Integrable (fun z:(History X k×Ω)×ℝ=>AP k (u z.1.2) z.1.1 z.1.2 z.2)
      (((historyMeasure R₀ ξ k).prod μ).prod volume):=by
  have hm:=ControlledReferenceFamilyDefectPoint.diagonal_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF hFm
      hsmall hΛ u hu k
  obtain ⟨K,hKn,hK⟩:=active_mass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hΛ k
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun z=>(hK (u z.2) z.1 z.2).1),?_⟩
  have hi:=((UncutHistoryMass.weight_integrable (Base (0,0)) ξ k).const_mul K).comp_fst μ
  apply hi.mono' hm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_of_nonneg (integral_nonneg (fun _=>norm_nonneg _))]
  exact (hK (u z.2) z.1 z.2).2

end SHE.ControlledReferenceFamilyDefectL1
