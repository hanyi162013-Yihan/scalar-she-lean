module

public import SHE.MixedJointLevelStep
public import SHE.MixedNativeJointHistory
public import SHE.JointInsertionIntegrability
public import SHE.JointWordDefect

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
noncomputable section

namespace SHE.MixedJointIntegratedLevel
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
variable {Ω P : Type*} [MeasurableSpace Ω] [MeasurableSpace P]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {R : ReferenceData} {n : ℕ} (L : Level R P n)
local notation "dU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U" => (dU).physicalState
local notation "V" => (dV).physicalState
local notation "XU" => (dU).physicalField
local notation "XV" => (dV).physicalField

local notation "D" => MixedJointLevelData.state 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L

local notation "leaf" => MixedJointLevelData.leaf 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L
local notation "ref" => MixedJointLevelData.reference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L
local notation "loc" => MixedJointLevelData.localRemainder 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L
local notation "mark" => MixedJointLevelData.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L

def noiseVersion (p : P) (ω : Ω) : ℝ := leaf p ω-ref p ω-loc p ω-mark p ω

theorem noiseVersion_measurable :
    Measurable (fun p : P×Ω => noiseVersion 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L p.1 p.2) :=
  (((MixedJointLevelData.leaf_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L).sub
    (MixedJointLevelData.reference_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L)).sub
    (MixedJointLevelData.localRemainder_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L)).sub
    (MixedJointLevelData.mark_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L)

theorem uniform_bound (hΛ : 0≤Λ) : ∃ K : ℝ,0≤K ∧ ∀ p ω,
    ‖leaf p ω‖≤K ∧ ‖ref p ω‖≤K ∧ ‖loc p ω‖≤K ∧ ‖mark p ω‖≤K ∧
    ‖noiseVersion 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L p ω‖≤K := by
  obtain ⟨A,hAn,hA⟩ := JointInsertionBounds.uniform_level_bound L Λ U V XU XV
  obtain ⟨B,hBn,hB⟩ := MixedJointLevelData.mark_uniform_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hΛ
  refine ⟨3*A+B,by positivity,fun p ω => ?_⟩
  have hl : ‖leaf p ω‖≤A := (hA p ω).1
  have hr : ‖ref p ω‖≤A := (hA p ω).2.1
  have hc : ‖loc p ω‖≤A := (hA p ω).2.2
  have hm := (hB p ω).1
  refine ⟨by linarith,by linarith,by linarith,by linarith,?_⟩
  dsimp only [noiseVersion]
  have hh := (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
    (add_le_add ((norm_sub_le _ _).trans (add_le_add hl hr)) hc)) hm)
  linarith only [hh]

variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
include hIJ₀ hIJ₁ in
theorem noiseVersion_centered (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J) (hΛ : 0≤Λ)
    (hA : R.totalVariance=(fun z => κ+aV z)) (hh : R.horizon≤(H:ℝ))
    {η : ℝ} (hη : 0<η) (hgap : ∀ p i,η≤(L.observations.observations p i).target-L.terminal p)
    (p : P) :
    Integrable (noiseVersion 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L p) μ ∧
      (∫ ω,noiseVersion 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L p ω ∂μ)=0 := by
  obtain ⟨N,hNi,hNc,hN⟩ := MixedJointLevelStep.one_step 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S L J hIJ₀ hIJ₁ hnull hJ hΛ hA hh hη hgap p
  have he : noiseVersion 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L p=ᵐ[μ] N := by
    filter_upwards [hN] with ω hω
    dsimp only [noiseVersion]
    linarith only [hω]
  exact ⟨hNi.congr he.symm,(integral_congr_ae he).trans hNc⟩

include hIJ₀ hIJ₁ in
/-- Genuine expected first-defect identity integrated over any finite
history measure. Every stochastic applicability premise is discharged
by the constructed mixed pair and the original universal Itô package.
The retained E mark is explicit and no infinite-depth limit is taken. -/
theorem expected_level (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J) (hΛ : 0≤Λ)
    (hA : R.totalVariance=(fun z => κ+aV z)) (hh : R.horizon≤(H:ℝ))
    {η : ℝ} (hη : 0<η) (hgap : ∀ p i,η≤(L.observations.observations p i).target-L.terminal p)
    (ν : Measure P) [IsFiniteMeasure ν] :
    (∫ q : P×Ω,leaf q.1 q.2 ∂ν.prod μ)=
      (∫ q : P×Ω,ref q.1 q.2 ∂ν.prod μ)+
      (∫ q : P×Ω,loc q.1 q.2 ∂ν.prod μ)+
      (∫ q : P×Ω,mark q.1 q.2 ∂ν.prod μ) := by
  obtain ⟨K,hKn,hK⟩ := uniform_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hΛ
  have hL : Integrable (fun q : P×Ω => leaf q.1 q.2) (ν.prod μ) :=
    (integrable_const K).mono' (MixedJointLevelData.leaf_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun q => (hK q.1 q.2).1))
  have hR : Integrable (fun q : P×Ω => ref q.1 q.2) (ν.prod μ) :=
    (integrable_const K).mono' (MixedJointLevelData.reference_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun q => (hK q.1 q.2).2.1))
  have hC : Integrable (fun q : P×Ω => loc q.1 q.2) (ν.prod μ) :=
    (integrable_const K).mono' (MixedJointLevelData.localRemainder_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun q => (hK q.1 q.2).2.2.1))
  have hM : Integrable (fun q : P×Ω => mark q.1 q.2) (ν.prod μ) :=
    (integrable_const K).mono' (MixedJointLevelData.mark_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun q => (hK q.1 q.2).2.2.2.1))
  have hN : Integrable (fun q : P×Ω => noiseVersion 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L q.1 q.2) (ν.prod μ) :=
    (integrable_const K).mono' (noiseVersion_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun q => (hK q.1 q.2).2.2.2.2))
  have hzero : (∫ q : P×Ω,noiseVersion 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L q.1 q.2 ∂ν.prod μ)=0 := by
    rw [integral_prod _ hN]
    have hz (p : P) := (noiseVersion_centered 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L
      J hIJ₀ hIJ₁ hnull hJ hΛ hA hh hη hgap p).2
    simp only [hz,integral_zero]
  have he₁ := integral_sub hL hR
  have he₂ := integral_sub (hL.sub hR) hC
  have he₃ := integral_sub ((hL.sub hR).sub hC) hM
  change (∫ q : P×Ω,leaf q.1 q.2-ref q.1 q.2-loc q.1 q.2-mark q.1 q.2 ∂ν.prod μ)=0 at hzero
  simp only [Pi.sub_apply] at he₁ he₂ he₃
  rw [he₃,he₂,he₁] at hzero
  linarith only [hzero]

end SHE.MixedJointIntegratedLevel
