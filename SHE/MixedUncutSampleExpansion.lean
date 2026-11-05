module

public import SHE.JointUncutSuccessor
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

namespace SHE.MixedUncutSampleExpansion
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
variable {Ω P : Type} [MeasurableSpace Ω] [MeasurableSpace P]
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

open CutoffWordHistories CutoffCarriers CutoffUncutComparison UncutWordEvaluation Classical

local notation "N"=>MixedUncutNoiseL2.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L
local notation "Mmark"=>MixedJointUncutMark.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L

def leafMass (ν:Measure P) (k:ℕ) (ω:Ω):ℝ:=
  ∫p,JointUncutWordEvaluation.leaf L Λ U V XU XV k p ω ∂historyMeasure R ν k

def referenceMass (ν:Measure P) (k:ℕ) (ω:Ω):ℝ:=
  ∫p,JointUncutWordEvaluation.reference L Λ U V XU XV k p ω ∂historyMeasure R ν k

def noiseMass (ν:Measure P) (k:ℕ) (ω:Ω):ℝ:=∫p,N k p ω ∂historyMeasure R ν k

def markMass (ν:Measure P) (k:ℕ) (ω:Ω):ℝ:=∫p,Mmark k p ω ∂historyMeasure R ν k

/-- The uncut canonical noise is the actual whole physical Ito defect.
The U/V coefficient mismatch remains inside its full retained mark. -/
theorem noise_eq (k:ℕ) (p:History P k) (ω:Ω):
    N k p ω=JointUncutWordEvaluation.leaf L Λ U V XU XV k p ω-
      JointUncutWordEvaluation.reference L Λ U V XU XV k p ω-
      JointUncutLocalRemainder.value L Λ U V XU XV k p ω-Mmark k p ω:=by
  have hl:JointUncutWordEvaluation.leaf L Λ U V XU XV k p ω=
      UncutSmoothWords.weight L k p*JointWordAnalytic.leaf (normalizedLevel L k) Λ U V XU XV p ω:=by
    rw [JointUncutWordEvaluation.leaf,UncutSmoothWords.test_eq_weight_normalized]
    rfl
  rw [hl,JointUncutWordEvaluation.reference_eq_weight]
  dsimp only [MixedUncutNoiseL2.value,MixedJointIntegratedLevel.noiseVersion,
    MixedJointLevelData.leaf,MixedJointLevelData.reference,MixedJointLevelData.localRemainder,
    JointUncutLocalRemainder.value,MixedJointUncutMark.mark]
  ring

/-- Every finite uncut recursion level is a samplewise cycle, with no
boundary correction or positive heat cutoff left over. -/
theorem sample_cycle (hΛ:0≤Λ) (ν:Measure P) [IsFiniteMeasure ν] (k:ℕ) (ω:Ω):
    leafMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L ν k ω=
      referenceMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L ν k ω+
      noiseMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L ν k ω+
      markMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L ν k ω+
      leafMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L ν (k+1) ω:=by
  let σ:=historyMeasure R ν k
  let W:=UncutSmoothWords.weight L k
  have hW:Integrable W σ:=UncutHistoryMass.weight_integrable L ν k
  have hint(f:History P k×Ω→ℝ)(hf:Measurable f)(C:ℝ)(hb:∀p ω,‖f (p,ω)‖≤C*W p):
      Integrable (fun p=>f (p,ω)) σ:=
    (hW.const_mul C).mono' (hf.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p=>hb p ω))
  obtain ⟨C,hC,hCl,hCr⟩:=JointUncutWordEvaluation.evaluation_norm_bounds L Λ U V XU XV k
  have hiL:=hint _ (JointUncutWordEvaluation.leaf_measurable L Λ
    (dU).physicalState_measurable (dV).physicalState_measurable
    (dU).physicalField_measurable (dV).physicalField_measurable k) C hCl
  have hiR:=hint _ (JointUncutWordEvaluation.reference_measurable L Λ
    (dU).physicalState_measurable (dV).physicalState_measurable
    (dU).physicalField_measurable (dV).physicalField_measurable k) C hCr
  obtain ⟨D,hD,hDb⟩:=JointUncutLocalRemainder.bound L Λ U V XU XV k
  have hmLoc:Measurable (fun z:History P k×Ω=>JointUncutLocalRemainder.value L Λ U V XU XV k z.1 z.2):=
    ((UncutSmoothWords.weight_measurable L k).comp measurable_fst).mul
      (JointWordAnalytic.remainder_measurable (normalizedLevel L k) Λ
        (dU).physicalState_measurable (dV).physicalState_measurable
        (dU).physicalField_measurable (dV).physicalField_measurable)
  have hiC:=hint _ hmLoc D hDb
  obtain ⟨B,hB,hBb⟩:=MixedJointUncutMark.mark_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hΛ k
  have hiM:=hint _ (MixedJointUncutMark.mark_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k) B hBb
  simp only [Prod.fst,Prod.snd] at hiL hiR hiC hiM
  have he:(∫p,N k p ω ∂σ)=(∫p,JointUncutWordEvaluation.leaf L Λ U V XU XV k p ω ∂σ)-
      (∫p,JointUncutWordEvaluation.reference L Λ U V XU XV k p ω ∂σ)-
      (∫p,JointUncutLocalRemainder.value L Λ U V XU XV k p ω ∂σ)-(∫p,Mmark k p ω ∂σ):=by
    simp_rw [noise_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L]
    have he1:=integral_sub hiL hiR
    have he2:=integral_sub (hiL.sub hiR) hiC
    have he3:=integral_sub ((hiL.sub hiR).sub hiC) hiM
    simp only [Pi.sub_apply] at he1 he2 he3
    linarith only [he1,he2,he3]
  have hs:=JointUncutSuccessor.averaged_eq L Λ U V XU XV
    (dU).physicalState_measurable (dV).physicalState_measurable
    (dU).physicalField_measurable (dV).physicalField_measurable ν k ω
  change (∫p,JointUncutWordEvaluation.leaf L Λ U V XU XV k p ω ∂σ)=_
  dsimp only [referenceMass,noiseMass,markMass,leafMass]
  linarith only [he,hs]

/-- The literal finite uncut physical recursion, before expectation.
Every stochastic term and every full mixed-coefficient mark survives. -/
theorem finite_expansion (hΛ:0≤Λ) (ν:Measure P) [IsFiniteMeasure ν] (depth:ℕ) (ω:Ω):
    leafMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L ν 0 ω=
      (∑k∈Finset.range depth,referenceMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L ν k ω)+
      (∑k∈Finset.range depth,noiseMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L ν k ω)+
      (∑k∈Finset.range depth,markMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L ν k ω)+
      leafMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L ν depth ω:=by
  induction depth with
  | zero=>simp
  | succ k ih=>
    have hs:=sample_cycle 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hΛ ν k ω
    simp only [Finset.sum_range_succ]
    linarith only [ih,hs]

end SHE.MixedUncutSampleExpansion
