module

public import SHE.MixedCanonicalRootOriginalIto
public import SHE.NativeScalarFourierWeight
public import SHE.NativeBesselFieldAE
public import SHE.ControlledReferenceFamilyResidual
public import SHE.PastParameterOriginalIto
public import SHE.PastItoLimitWitness
public import SHE.HistoryMeasureGeometry

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false

namespace SHE.MixedCanonicalRootHilbertExpansion
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
local instance mixedCanonicalRootHilbertExpansion_circleSecondCountable : SecondCountableTopology StoppedFourier.CircleL2 :=
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

local notation "Field"=>MixedCanonicalRootFields.field
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF hFm
local notation "D"=>MixedCanonicalRootFields.residual
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF hFm

variable (hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)

def term (i:Fin 3)(k:ℕ)(ω:Ω):CircleL2:=
  NativeBesselFieldAE.value Λ ρ hL hρ (fun z:Ω×HeatCircle=>(Field i k z:ℂ)) ω
local notation "Term"=>term 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF hFm hL hρ
local notation "Noise"=>MixedCanonicalRootOriginalIto.value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF hFm hL hρ

include hsmall in
theorem term_measurable (i:Fin 3)(k:ℕ):Measurable (Term i k):=
  NativeBesselFieldAE.measurable Λ ρ hL hρ _ (Complex.continuous_ofReal.measurable.comp
    (MixedCanonicalRootFields.field_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hsmall (zero_le_one.trans hL) i k))

include hsmall hL hρ in
theorem field_section_memLp (i:Fin 3)(k:ℕ)(ω:Ω):
    MemLp (fun x:HeatCircle=>(Field i k (ω,x):ℂ)) 2 AddCircle.haarAddCircle:=by
  obtain ⟨C,hC,hCb⟩:=MixedCanonicalRootFields.field_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall (zero_le_one.trans hL) k
  have hm:Measurable (fun x:HeatCircle=>(Field i k (ω,x):ℂ)):=Complex.continuous_ofReal.measurable.comp
    ((MixedCanonicalRootFields.field_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hsmall (zero_le_one.trans hL) i k).comp
        (measurable_const.prodMk measurable_id))
  exact MemLp.of_bound hm.aestronglyMeasurable C (ae_of_all _ (fun x=>by
    simpa only [Complex.norm_real] using hCb i (ω,x)))

include hsmall in
/-- Actual zero-root-gap finite stochastic telescope in native Hilbert
space. The noise is the genuine random-reference original-J residual,
not a substitute field introduced to meet an energy budget. -/
theorem finite_expansion (depth:ℕ)(ω:Ω):
    Term 0 0 ω=(∑k∈Finset.range depth,Term 1 k ω)+Noise depth ω+
      (∑k∈Finset.range depth,Term 2 k ω)+Term 0 depth ω:=by
  let G:Sum (Fin depth×Fin 2) (Fin 2)→Ω×HeatCircle→ℂ:=fun i z=>
    match i with
    | Sum.inl (k,j)=>(Field j.succ k z:ℂ)
    | Sum.inr j=>if j=0 then (D depth z:ℂ) else (Field 0 depth z:ℂ)
  have hFieldM(i:Fin 3)(k:ℕ):Measurable (fun z:Ω×HeatCircle=>(Field i k z:ℂ)):=
    Complex.continuous_ofReal.measurable.comp (MixedCanonicalRootFields.field_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hsmall (zero_le_one.trans hL) i k)
  have hDm:Measurable (fun z:Ω×HeatCircle=>(D depth z:ℂ)):=
    Complex.continuous_ofReal.measurable.comp (MixedCanonicalRootFields.residual_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hsmall (zero_le_one.trans hL) depth)
  have hG(i:Sum (Fin depth×Fin 2) (Fin 2)):Measurable (G i):=by
    cases i with
    | inl i=>exact hFieldM i.2.succ i.1
    | inr j=>
      by_cases hj:j=0
      · simpa only [G,hj,↓reduceIte] using hDm
      · simpa only [G,hj,↓reduceIte] using hFieldM 0 depth
  have hp(i:Sum (Fin depth×Fin 2) (Fin 2)):
      MemLp (fun x=>G i (ω,x)) 2 AddCircle.haarAddCircle:=by
    cases i with
    | inl i=>
      exact field_section_memLp
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hL hρ i.2.succ i.1 ω
    | inr j=>
      by_cases hj:j=0
      · simp only [G,hj,↓reduceIte]
        exact (MixedCanonicalRootOriginalIto.section_memLp
            𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
            P hAs θ v b hvb Z htarget hstop F hF hFm hsmall (zero_le_one.trans hL) depth ω).ofReal
      · simpa only [G,hj,↓reduceIte] using field_section_memLp
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
          P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hL hρ 0 depth ω
  have h01:(0:Fin 2).succ=(1:Fin 3):=rfl
  have h12:(1:Fin 2).succ=(2:Fin 3):=rfl
  have h10:(1:Fin 2)≠0:=by decide
  have he:∀ᵐx∂AddCircle.haarAddCircle,(Field 0 0 (ω,x):ℂ)=
      ∑i:Sum (Fin depth×Fin 2) (Fin 2),G i (ω,x):=by
    filter_upwards with x
    have hr:Field 0 0 (ω,x)=(∑k∈Finset.range depth,Field 1 k (ω,x))+
        (∑k∈Finset.range depth,Field 2 k (ω,x))+D depth (ω,x)+Field 0 depth (ω,x):=by
      unfold MixedCanonicalRootFields.residual
      ring
    have hc:=congrArg (fun r:ℝ=>(r:ℂ)) hr
    push_cast at hc
    simpa only [G,Fintype.sum_sum_type,Fintype.sum_prod_type,Fin.sum_univ_two,h01,h12,h10,↓reduceIte,
      Finset.sum_add_distrib,add_zero,←Fin.sum_univ_eq_sum_range,add_assoc] using hc
  have ht:=NativeBesselFiniteIdentity.finite_sum Λ ρ hL hρ Finset.univ
    (fun z:Ω×HeatCircle=>(Field 0 0 z:ℂ)) (hFieldM 0 0) G hG ω
    (field_section_memLp 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hL hρ 0 0 ω)
    (fun i _=>hp i) he
  simpa only [term,MixedCanonicalRootOriginalIto.value,G,Fintype.sum_sum_type,Fintype.sum_prod_type,
    Fin.sum_univ_two,h01,h12,h10,↓reduceIte,Finset.sum_add_distrib,add_zero,←Fin.sum_univ_eq_sum_range,add_assoc,add_left_comm,add_comm] using ht

end SHE.MixedCanonicalRootHilbertExpansion
