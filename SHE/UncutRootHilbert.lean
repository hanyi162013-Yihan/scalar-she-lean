module

public import SHE.JointUncutSuccessor
public import SHE.MixedUncutSampleExpansion
public import SHE.RootSectionAverage
public import SHE.UncutRootFields
public import SHE.NativeBesselFiniteIdentity
public import SHE.NativeBesselFieldAE
public import SHE.MixedUncutNoiseL2
public import SHE.MixedJointUncutMark

public import SHE.MixedNoiseTestScaling
public import SHE.WeightedHistoryL2Limit
public import SHE.JointDefectScaling
public import SHE.UncutWordEvaluation
public import SHE.DominatedCutoffLimit
public import SHE.JointRecursiveHessian
public import SHE.NativeRowTargetContinuity
public import SHE.MixedNativeJointHistory
public import SHE.JointInsertionIntegrability
public import SHE.JointWordDefect

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
noncomputable section

namespace SHE.UncutRootHilbert
open MeasureTheory Set PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation CutoffWordLevel
open GaussianTaylorAverage JointWordAnalytic
open scoped ENNReal NNReal
local instance mixedJointUncutMarkInstance1 : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance mixedJointUncutMarkInstance2 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedJointUncutMarkInstance3 : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance mixedJointUncutMarkInstance4 : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance mixedJointUncutMarkInstance5 : MeasurableSpace CircleL2 := borel _
local instance mixedJointUncutMarkInstance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedJointUncutMarkInstance7 : MeasurableSpace RealL2 := borel _
local instance mixedJointUncutMarkInstance8 : BorelSpace RealL2 := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {R : ReferenceData} {n : ℕ} (L : Level R HeatCircle n)
local notation "dU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U" => (dU).physicalState
local notation "V" => (dV).physicalState
local notation "XU" => (dU).physicalField
local notation "XV" => (dV).physicalField

open CutoffWordHistories CutoffCarriers CutoffUncutComparison UncutWordEvaluation Classical

local notation "Field"=>UncutRootFields.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L
local notation "FieldM"=>UncutRootFields.field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L
variable (hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)

def value (i:Fin 4)(k:ℕ)(ω:Ω):CircleL2:=
  NativeBesselFieldAE.value Λ ρ hL hρ (fun z:Ω×HeatCircle=>(Field i k z:ℂ)) ω
local notation "Value"=>value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hL hρ

theorem measurable (i:Fin 4)(k:ℕ):Measurable (Value i k):=
  NativeBesselFieldAE.measurable Λ ρ hL hρ _ (Complex.continuous_ofReal.measurable.comp (FieldM i k))

include hL in
theorem section_memLp (i:Fin 4)(k:ℕ)(ω:Ω):
    MemLp (fun x:HeatCircle=>(Field i k (ω,x):ℂ)) 2 AddCircle.haarAddCircle:=by
  obtain ⟨C,hC,hCb⟩:=UncutRootFields.field_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L
    (zero_le_one.trans hL) k
  apply MemLp.of_bound
    ((Complex.continuous_ofReal.measurable.comp (FieldM i k)).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable C
  filter_upwards with x
  change ‖(Field i k (ω,x):ℂ)‖≤C
  simpa only [Complex.norm_real] using hCb i (ω,x)

/-- A genuine finite Hilbert-valued uncut telescope, including zero
initial root heat gap. Every field is Borel and all spatial L2 sections
are derived. The noise field is the original recursive physical defect;
its zero-gap SAME-J identification is a separate stochastic obligation. -/
theorem finite_expansion (depth:ℕ)(ω:Ω):
    Value 0 0 ω=(∑k∈Finset.range depth,Value 1 k ω)+
      (∑k∈Finset.range depth,Value 2 k ω)+(∑k∈Finset.range depth,Value 3 k ω)+Value 0 depth ω:=by
  classical
  have h01:(0:Fin 3).succ=(1:Fin 4):=by decide
  have h12:((0:Fin 2).succ).succ=(2:Fin 4):=by decide
  have h23:(((default:Fin 1).succ).succ).succ=(3:Fin 4):=by decide
  let G:Sum (Fin depth×Fin 3) Unit→Ω×HeatCircle→ℂ:=fun i z=>
    match i with
    | Sum.inl (k,j)=>(Field j.succ k z:ℂ)
    | Sum.inr _=>(Field 0 depth z:ℂ)
  have hG(i:Sum (Fin depth×Fin 3) Unit):Measurable (G i):=by
    cases i with
    | inl i=>exact Complex.continuous_ofReal.measurable.comp (FieldM i.2.succ i.1)
    | inr _=>exact Complex.continuous_ofReal.measurable.comp (FieldM 0 depth)
  have hp(i:Sum (Fin depth×Fin 3) Unit):MemLp (fun x=>G i (ω,x)) 2 AddCircle.haarAddCircle:=by
    cases i with
    | inl i=>exact section_memLp 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hL i.2.succ i.1 ω
    | inr _=>exact section_memLp 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hL 0 depth ω
  have he:∀ᵐx∂AddCircle.haarAddCircle,(Field 0 0 (ω,x):ℂ)=∑i:Sum (Fin depth×Fin 3) Unit,G i (ω,x):=by
    filter_upwards with x
    have hh:=congrArg (fun r:ℝ=>(r:ℂ)) (UncutRootFields.finite_expansion 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S L (zero_le_one.trans hL) depth (ω,x))
    push_cast at hh
    simpa only [G,Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_unique,
      Fin.sum_univ_succ,Finset.sum_add_distrib,add_zero,←Fin.sum_univ_eq_sum_range,add_assoc,h01,h12,h23] using hh
  have ht:=NativeBesselFiniteIdentity.finite_sum Λ ρ hL hρ Finset.univ
    (fun z:Ω×HeatCircle=>(Field 0 0 z:ℂ)) (Complex.continuous_ofReal.measurable.comp (FieldM 0 0))
    G hG ω (section_memLp 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hL 0 0 ω)
    (fun i _=>hp i) he
  simpa only [value,G,Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_unique,
    Fin.sum_univ_succ,Finset.sum_add_distrib,add_zero,←Fin.sum_univ_eq_sum_range,add_assoc,h01,h12,h23] using ht
end SHE.UncutRootHilbert
