module

public import SHE.JointUncutSuccessor
public import SHE.MixedUncutSampleExpansion
public import SHE.RootSectionAverage
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

namespace SHE.UncutRootFields
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

/-- Literal original leaf/reference/noise/full mixed mark, respectively. -/
def raw (i:Fin 4)(k:ℕ)(z:History HeatCircle k×Ω):ℝ:=
  match i with
  | 0=>JointUncutWordEvaluation.leaf L Λ U V XU XV k z.1 z.2
  | 1=>JointUncutWordEvaluation.reference L Λ U V XU XV k z.1 z.2
  | 2=>MixedUncutNoiseL2.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k z.1 z.2
  | _=>MixedJointUncutMark.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k z.1 z.2
local notation "Raw"=>raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L

def field (i:Fin 4)(k:ℕ):Ω×HeatCircle→ℝ:=
  RootSectionAverage.average R k (fun z=>Raw i k (z.2,z.1))
local notation "Field"=>field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L

theorem raw_measurable (i:Fin 4)(k:ℕ):Measurable (Raw i k):=by
  fin_cases i
  · exact JointUncutWordEvaluation.leaf_measurable L Λ (dU).physicalState_measurable (dV).physicalState_measurable
      (dU).physicalField_measurable (dV).physicalField_measurable k
  · exact JointUncutWordEvaluation.reference_measurable L Λ (dU).physicalState_measurable (dV).physicalState_measurable
      (dU).physicalField_measurable (dV).physicalField_measurable k
  · exact MixedUncutNoiseL2.value_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k
  · exact MixedJointUncutMark.mark_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k

theorem field_measurable (i:Fin 4)(k:ℕ):Measurable (Field i k):=
  RootSectionAverage.measurable R k _ ((raw_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L i k).comp measurable_swap)

theorem raw_bound (hΛ:0≤Λ)(k:ℕ):∃C:ℝ,0≤C ∧
    ∀(i:Fin 4) p ω,‖Raw i k (p,ω)‖≤C*UncutSmoothWords.weight L k p:=by
  obtain ⟨C,hC,hCl,hCr⟩:=JointUncutWordEvaluation.evaluation_norm_bounds L Λ U V XU XV k
  obtain ⟨D,hD,hDb⟩:=MixedUncutNoiseL2.bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hΛ k
  obtain ⟨E,hE,hEb⟩:=MixedJointUncutMark.mark_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hΛ k
  refine ⟨C+D+E,by linarith,?_⟩
  intro i p ω
  have hw:=UncutSmoothWords.weight_nonneg L k p
  fin_cases i
  · exact (hCl p ω).trans (mul_le_mul_of_nonneg_right (by linarith) hw)
  · exact (hCr p ω).trans (mul_le_mul_of_nonneg_right (by linarith) hw)
  · exact (hDb p ω).trans (mul_le_mul_of_nonneg_right (by linarith) hw)
  · exact (hEb p ω).trans (mul_le_mul_of_nonneg_right (by linarith) hw)

/-- All original uncut terms retain a jointly Borel spatial output and
uniform finite-depth bound. Constants may depend on smooth coefficient
jets and depth; no rough all-order estimate is asserted here. -/
theorem field_bound (hΛ:0≤Λ)(k:ℕ):∃C:ℝ,0≤C ∧∀(i:Fin 4) z,‖Field i k z‖≤C:=by
  obtain ⟨C,hC,hCb⟩:=raw_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hΛ k
  refine ⟨C*UncutHistoryMass.massBound (R:=R) (n:=n) (AddCircle.haarAddCircle:Measure HeatCircle) k,
    mul_nonneg hC (UncutHistoryMass.massBound_nonneg _ k),?_⟩
  intro i z
  exact RootSectionAverage.norm_le L k (fun a=>Raw i k (a.2,a.1))
    ((raw_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L i k).comp measurable_swap)
    C hC (fun ω p=>hCb i p ω) z.1 z.2

theorem field_eq_mass (hΛ:0≤Λ)(i:Fin 4)(k:ℕ)(ω:Ω)(x:HeatCircle):
    Field i k (ω,x)=∫p,Raw i k (p,ω) ∂historyMeasure R (Measure.dirac x) k:=by
  obtain ⟨C,hC,hCb⟩:=raw_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hΛ k
  have hi:Integrable (fun p=>Raw i k (p,ω)) (historyMeasure R (Measure.dirac x) k):=
    ((UncutHistoryMass.weight_integrable L (Measure.dirac x) k).const_mul C).mono'
      ((raw_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L i k).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p=>hCb i p ω))
  exact (RootSectionAverage.integral_dirac_history R k x _ hi).symm

/-- Actual uncut finite sample expansion with the original output root
retained, before expectation or spatial contraction. This algebraic
identity retains the full mixed coefficient mark and terminal leaf. -/
theorem finite_expansion (hΛ:0≤Λ)(depth:ℕ)(z:Ω×HeatCircle):
    Field 0 0 z=(∑k∈Finset.range depth,Field 1 k z)+
      (∑k∈Finset.range depth,Field 2 k z)+(∑k∈Finset.range depth,Field 3 k z)+Field 0 depth z:=by
  simp_rw [field_eq_mass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hΛ]
  exact MixedUncutSampleExpansion.finite_expansion 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hΛ
    (Measure.dirac z.2) depth z.1
end SHE.UncutRootFields
