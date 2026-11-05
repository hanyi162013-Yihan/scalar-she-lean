module

public import SHE.MixedCanonicalUncutOriginalNoise
public import SHE.ControlledReferenceFamilyResidual
public import SHE.PastParameterOriginalIto
public import SHE.PastItoLimitWitness
public import SHE.HistoryMeasureGeometry
public import SHE.RootSectionAverage
public import SHE.NativeBesselFiniteIdentity

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false

namespace SHE.MixedCanonicalRootFields
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
local instance mixedCanonicalRootFields_circleSecondCountable : SecondCountableTopology StoppedFourier.CircleL2 :=
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
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformSmooth.UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : HeatCircle×WordRecursion.State 1 => F q.1 q.2))


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
local notation "LS" => ControlledReferenceFamilySections.leafSection 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF hFm
local notation "RS" => ControlledReferenceFamilySections.referenceSection 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF hFm
local notation "MS" => ControlledReferenceFamilySections.markSection 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF hFm

local notation "K" => ControlledReferenceFamilyResidual.residual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF hFm
local notation "N" => (fun p:Inputs=>MixedUncutSampleExpansion.noiseMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p))

local notation "R₀" => referenceData P (fun z=>κ+aV z) hAs Λ θ v b hvb (0,0)

/-- Literal diagonal leaf, reference and full mixed mark. The actual
past states are inside every Gaussian law and recursively moving test. -/
def raw (i:Fin 3)(k:ℕ)(z:History HeatCircle k×Ω):ℝ:=
  match i with
  | 0=>JointUncutWordEvaluation.leaf (Base (pastParameter z.2)) Λ U V XU XV k z.1 z.2
  | 1=>JointUncutWordEvaluation.reference (Base (pastParameter z.2)) Λ U V XU XV k z.1 z.2
  | _=>MixedJointUncutMark.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (Base (pastParameter z.2)) k z.1 z.2
local notation "Raw"=>raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF hFm

def field (i:Fin 3)(k:ℕ):Ω×HeatCircle→ℝ:=
  RootSectionAverage.average R₀ k (fun z=>Raw i k (z.2,z.1))
local notation "Field"=>field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF hFm

include hsmall in
theorem raw_measurable (hΛ:0≤Λ)(i:Fin 3)(k:ℕ):Measurable (Raw i k):=by
  have hu:=MixedNativeRandomReferenceStep.randomParameter_stronglyMeasurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
  have hu' : StronglyMeasurable pastParameter := hu.mono (𝓕.le v)
  have hL:=ControlledReferenceFamilyEvaluation.diagonal_measurable P (fun z=>κ+aV z) hAs Λ θ v b hvb
    Z htarget hstop F hF hFm hsmall U V XU XV
    (dU).physicalState_measurable (dV).physicalState_measurable
    (dU).physicalField_measurable (dV).physicalField_measurable hΛ pastParameter hu' k
  have hM:=ControlledReferenceFamilyMark.diagonal_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hΛ pastParameter hu' k
  fin_cases i
  · exact hL.1
  · exact hL.2
  · exact hM

include hsmall in
theorem field_measurable (hΛ:0≤Λ)(i:Fin 3)(k:ℕ):Measurable (Field i k):=
  RootSectionAverage.measurable R₀ k _ ((raw_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hΛ i k).comp measurable_swap)

theorem raw_bound (hΛ:0≤Λ)(k:ℕ):∃C:ℝ,0≤C ∧
    ∀(i:Fin 3) h ω,‖Raw i k (h,ω)‖≤C*UncutSmoothWords.weight (Base (0,0)) k h:=by
  obtain ⟨C,hC,hCb⟩:=ControlledReferenceFamilyEvaluation.evaluation_bound
    P (fun z=>κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF hFm U V XU XV k
  obtain ⟨D,hD,hDb⟩:=ControlledReferenceFamilyMark.mark_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hΛ k
  refine ⟨C+D,add_nonneg hC hD,?_⟩
  intro i h ω
  have hw:=UncutSmoothWords.weight_nonneg (Base (0,0)) k h
  fin_cases i
  · exact (hCb (pastParameter ω) h ω).1.trans (mul_le_mul_of_nonneg_right (by linarith) hw)
  · exact (hCb (pastParameter ω) h ω).2.trans (mul_le_mul_of_nonneg_right (by linarith) hw)
  · exact (hDb (pastParameter ω) h ω).trans (mul_le_mul_of_nonneg_right (by linarith) hw)

include hsmall in
theorem field_bound (hΛ:0≤Λ)(k:ℕ):∃C:ℝ,0≤C ∧∀(i:Fin 3) z,‖Field i k z‖≤C:=by
  obtain ⟨C,hC,hCb⟩:=raw_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hΛ k
  refine ⟨C*UncutHistoryMass.massBound (R:=R₀) (n:=1) (AddCircle.haarAddCircle:Measure HeatCircle) k,
    mul_nonneg hC (UncutHistoryMass.massBound_nonneg _ k),?_⟩
  intro i z
  exact RootSectionAverage.norm_le (Base (0,0)) k (fun a=>Raw i k (a.2,a.1))
    ((raw_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hΛ i k).comp measurable_swap)
    C hC (fun ω p=>hCb i p ω) z.1 z.2

include hsmall in
theorem field_integral (hΛ:0≤Λ)(ν:Measure HeatCircle)[IsFiniteMeasure ν]
    (i:Fin 3)(k:ℕ)(ω:Ω):
    (∫x:HeatCircle,Field i k (ω,x) ∂ν)=∫h,Raw i k (h,ω) ∂historyMeasure R₀ ν k:=by
  obtain ⟨C,hC,hCb⟩:=raw_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hΛ k
  have hm:=raw_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hΛ i k
  have hi:Integrable (fun h=>Raw i k (h,ω)) (historyMeasure R₀ ν k):=
    ((UncutHistoryMass.weight_integrable (Base (0,0)) ν k).const_mul C).mono'
      (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (ae_of_all _ (fun h=>hCb i h ω))
  exact (RootSectionAverage.integral_history R₀ ν k (fun z=>Raw i k (z.2,z.1)) ω hi).symm

/-- Actual whole finite stochastic residual with the original native
spatial root retained, before applying the Bessel multiplier. -/
def residual (depth:ℕ)(z:Ω×HeatCircle):ℝ:=
  Field 0 0 z-(∑k∈Finset.range depth,Field 1 k z)-
    (∑k∈Finset.range depth,Field 2 k z)-Field 0 depth z
local notation "Residual"=>residual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF hFm

include hsmall in
theorem residual_measurable (hΛ:0≤Λ)(depth:ℕ):Measurable (Residual depth):=by
  have hm:=field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hΛ
  exact (((hm 0 0).sub (Finset.measurable_fun_sum _ (fun k _=>hm 1 k))).sub
    (Finset.measurable_fun_sum _ (fun k _=>hm 2 k))).sub (hm 0 depth)

include hsmall in
theorem field_integrable (hΛ:0≤Λ)(ν:Measure HeatCircle)[IsFiniteMeasure ν]
    (i:Fin 3)(k:ℕ)(ω:Ω):Integrable (fun x=>Field i k (ω,x)) ν:=by
  obtain ⟨C,hC,hCb⟩:=field_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hΛ k
  exact (integrable_const C).mono'
    ((field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hΛ i k).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (ae_of_all _ (fun x=>hCb i (ω,x)))

include hsmall in
theorem residual_integral (hΛ:0≤Λ)(ν:Measure HeatCircle)[IsFiniteMeasure ν]
    (depth:ℕ)(ω:Ω):
    (∫x:HeatCircle,Residual depth (ω,x) ∂ν)=K ν depth (pastParameter ω) ω:=by
  have hi:=field_integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hΛ ν
  have hR:=integrable_finset_sum (Finset.range depth) (fun k _=>hi 1 k ω)
  have hM:=integrable_finset_sum (Finset.range depth) (fun k _=>hi 2 k ω)
  unfold residual
  have hA:=integral_sub (((hi 0 0 ω).sub hR).sub hM) (hi 0 depth ω)
  have hB:=integral_sub ((hi 0 0 ω).sub hR) hM
  have hC:=integral_sub (hi 0 0 ω) hR
  simp only [Pi.sub_apply] at hA hB hC
  rw [hA,hB,hC,
    integral_finset_sum _ (fun k _=>hi 1 k ω),integral_finset_sum _ (fun k _=>hi 2 k ω)]
  simp_rw [field_integral 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hΛ ν]
  rfl

end SHE.MixedCanonicalRootFields
