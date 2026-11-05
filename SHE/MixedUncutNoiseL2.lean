module

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

namespace SHE.MixedUncutNoiseL2
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

open CutoffWordHistories CutoffCarriers CutoffUncutComparison RecursiveHeatBounds Filter Topology
open UncutWordEvaluation Classical
local notation "D" => MixedJointLevelData.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "Mmark" => MixedJointLevelData.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S


local notation "N"=>MixedJointIntegratedLevel.noiseVersion 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S

def value (k:ℕ) (p:History P k) (ω:Ω):ℝ:=UncutSmoothWords.weight L k p*N (normalizedLevel L k) p ω

def cutoff (δ:ℝ) (k:ℕ) (p:History P k) (ω:Ω):ℝ:=if hδ:0<δ then N (level L δ hδ 0 k) p ω else 0

local notation "NV"=>value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L
local notation "NC"=>cutoff 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L

theorem cutoff_eq {δ:ℝ} (hδ:0<δ) (k:ℕ) (p:History P k) (ω:Ω):
    NC δ k p ω=if Active L δ k p then NV k p ω else 0:=by
  rw [cutoff,dite_eq_left hδ]
  by_cases hp:Active L δ k p
  · rw [if_pos hp]
    apply MixedNoiseTestScaling.noise_smul 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (level L δ hδ 0 k) (normalizedLevel L k) (UncutSmoothWords.weight L k p) p ω
      (observations_eq L hδ zero_lt_one k p) (CutoffCarriers.terminal_eq L hδ zero_lt_one k p)
    rw [test_eq_active L hδ k p,if_pos hp,UncutSmoothWords.test_eq_weight_normalized]
    rfl
  · rw [if_neg hp]
    have hh:=MixedNoiseTestScaling.noise_smul 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (level L δ hδ 0 k) (normalizedLevel L k) 0 p ω
      (observations_eq L hδ zero_lt_one k p) (CutoffCarriers.terminal_eq L hδ zero_lt_one k p)
      (by rw [test_eq_active L hδ k p,if_neg hp,zero_smul])
    simpa only [zero_mul] using hh

theorem bound (hΛ:0≤Λ) (k:ℕ):∃C:ℝ,0≤C ∧ ∀p ω,‖NV k p ω‖≤C*UncutSmoothWords.weight L k p:=by
  obtain ⟨C,hC,hCb⟩:=MixedJointIntegratedLevel.uniform_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (normalizedLevel L k) hΛ
  refine ⟨C,hC,fun p ω=>?_⟩
  rw [value,norm_mul,Real.norm_eq_abs,abs_of_nonneg (UncutSmoothWords.weight_nonneg L k p)]
  exact (mul_le_mul_of_nonneg_left (hCb p ω).2.2.2.2 (UncutSmoothWords.weight_nonneg L k p)).trans_eq (mul_comm _ _)

theorem value_measurable (k:ℕ):Measurable (fun z:History P k×Ω=>NV k z.1 z.2):=
  ((UncutSmoothWords.weight_measurable L k).comp measurable_fst).mul
    (MixedJointIntegratedLevel.noiseVersion_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (normalizedLevel L k))

/-- Strong time-gap removal for the COMPLETE actual physical noise.
The pointwise test identity preserves all mixed bracket defects and
uses only the genuine integrable old-history weight before averaging. -/
theorem averaged_limit (hΛ:0≤Λ) (ν:Measure P) [IsFiniteMeasure ν] (k:ℕ):
    let E:=fun δ:ℝ=>fun ω=>∫p,NC δ k p ω-NV k p ω ∂historyMeasure R ν k
    (∀δ,Integrable (fun ω=>‖E δ ω‖^2) μ) ∧
      Tendsto (fun δ=>∫ω,‖E δ ω‖^2 ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0):=by
  obtain ⟨C,hC,hCb⟩:=bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hΛ k
  let W:=UncutSmoothWords.weight L k
  have hW:Integrable W (historyMeasure R ν k):=UncutHistoryMass.weight_integrable L ν k
  have hm:=value_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k
  have hfm(δ:ℝ):Measurable (fun z:History P k×Ω=>NC δ k z.1 z.2):=by
    by_cases hδ:0<δ
    · simpa only [cutoff,dite_eq_left hδ] using
        MixedJointIntegratedLevel.noiseVersion_measurable
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (level L δ hδ 0 k)
    · simp only [cutoff,dite_eq_right hδ]
      exact measurable_const
  have hb(δ:ℝ)(p:History P k)(ω:Ω):‖NC δ k p ω‖≤C*W p:=by
    by_cases hδ:0<δ
    · rw [cutoff_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hδ]
      split_ifs
      · exact hCb p ω
      · exact (norm_zero).le.trans (mul_nonneg hC (UncutSmoothWords.weight_nonneg L k p))
    · rw [cutoff,dite_eq_right hδ,norm_zero]
      exact mul_nonneg hC (UncutSmoothWords.weight_nonneg L k p)
  have he(z:History P k×Ω):∃η:ℝ,0<η ∧ ∀δ>0,δ<η→NC δ k z.1 z.2=NV k z.1 z.2:=by
    obtain ⟨η,hη,hEq⟩:=eventually_test_eq L k z.1
    refine ⟨η,hη,fun δ hδ hd=>?_⟩
    rw [cutoff,dite_eq_left hδ]
    apply MixedNoiseTestScaling.noise_smul 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (level L δ hδ 0 k) (normalizedLevel L k) (UncutSmoothWords.weight L k z.1) z.1 z.2
      (observations_eq L hδ zero_lt_one k z.1) (CutoffCarriers.terminal_eq L hδ zero_lt_one k z.1)
    rw [hEq δ hδ hd,UncutSmoothWords.test_eq_weight_normalized]
    rfl
  have ht:=DominatedCutoffLimit.integral_abs_sub_tendsto_zero ((historyMeasure R ν k).prod μ)
    (W:=fun z=>W z.1) (M:=C) (hW.comp_fst μ) hm (fun δ _=>hfm δ)
    (fun z=>hCb z.1 z.2) (fun δ _ z=>hb δ z.1 z.2) he
  exact WeightedHistoryL2Limit.averaged_limit (historyMeasure R ν k) μ
    (fun δ:ℝ=>fun z=>NC δ k z.1 z.2) (fun z=>NV k z.1 z.2) hfm hm W hW
    (UncutSmoothWords.weight_nonneg L k) hC hb hCb (𝓝[>] (0:ℝ))
    (by simpa only [Real.norm_eq_abs] using ht)

end SHE.MixedUncutNoiseL2
