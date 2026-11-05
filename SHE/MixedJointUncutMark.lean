module

public import SHE.MixedJointLevelData
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

namespace SHE.MixedJointUncutMark
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

def mark (k : ℕ) (p : History P k) (ω : Ω) : ℝ :=
  UncutSmoothWords.weight L k p*Mmark (normalizedLevel L k) p ω

def cutoffMark (δ : ℝ) (k : ℕ) (p : History P k) (ω : Ω) : ℝ :=
  if hδ : 0<δ then Mmark (level L δ hδ 0 k) p ω else 0

local notation "UM" => mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L
local notation "CM" => cutoffMark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L

theorem defect_eq_normalized {δ : ℝ} (hδ : 0<δ) (k : ℕ) (p : History P k) (ω : Ω) (t : ℝ) :
    D (level L δ hδ 0 k) ((p,ω),t)=D (normalizedLevel L k) ((p,ω),t) := by
  unfold MixedJointLevelData.defect
  rw [observations_eq L hδ zero_lt_one k p]
  rfl

theorem mark_eq_of_test {δ w : ℝ} (hδ : 0<δ) (k : ℕ) (p : History P k) (ω : Ω)
    (hF : (level L δ hδ 0 k).test p=w • (normalizedLevel L k).test p) :
    Mmark (level L δ hδ 0 k) p ω=w*Mmark (normalizedLevel L k) p ω :=
  JointDefectScaling.mark_eq_of_test_smul (level L δ hδ 0 k) (normalizedLevel L k) Λ U V XU XV
    (D (level L δ hδ 0 k)) (D (normalizedLevel L k)) w p ω
    (observations_eq L hδ zero_lt_one k p) (CutoffCarriers.terminal_eq L hδ zero_lt_one k p) hF
    (defect_eq_normalized 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hδ k p ω)

theorem cutoff_mark_eq {δ : ℝ} (hδ : 0<δ) (k : ℕ) (p : History P k) (ω : Ω) :
    CM δ k p ω=if Active L δ k p then UM k p ω else 0 := by
  classical
  rw [cutoffMark,dif_pos hδ]
  by_cases hp : Active L δ k p
  · rw [if_pos hp]
    apply mark_eq_of_test 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hδ k p ω
    rw [test_eq_active L hδ k p,if_pos hp,UncutSmoothWords.test_eq_weight_normalized]
    rfl
  · rw [if_neg hp]
    have he := mark_eq_of_test 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hδ k p ω
      (w := 0) (by rw [test_eq_active L hδ k p,if_neg hp,zero_smul])
    simpa only [zero_mul] using he

theorem mark_measurable (k : ℕ) : Measurable (fun q : History P k×Ω => UM k q.1 q.2) :=
  ((UncutSmoothWords.weight_measurable L k).comp measurable_fst).mul
    (MixedJointLevelData.mark_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (normalizedLevel L k))

/-- The signed physical mark has the actual integrable uncut history
weight as a majorant. No inverse covariance or cutoff derivative norm is
substituted for this weight. -/
theorem mark_bound (hΛ : 0≤Λ) (k : ℕ) : ∃ K : ℝ,0≤K ∧ ∀ p ω,
    ‖UM k p ω‖≤K*UncutSmoothWords.weight L k p := by
  obtain ⟨K,hK,hKb⟩ := MixedJointLevelData.mark_uniform_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (normalizedLevel L k) hΛ
  refine ⟨K,hK,fun p ω => ?_⟩
  rw [mark,norm_mul,Real.norm_eq_abs,abs_of_nonneg (UncutSmoothWords.weight_nonneg L k p)]
  exact (mul_le_mul_of_nonneg_left (hKb p ω).1 (UncutSmoothWords.weight_nonneg L k p)).trans_eq (mul_comm _ _)

theorem mark_eventually_eq (k : ℕ) (p : History P k) (ω : Ω) :
    ∃ η : ℝ,0<η ∧ ∀ δ>0,δ<η→CM δ k p ω=UM k p ω := by
  obtain ⟨η,hη,hEq⟩ := eventually_test_eq L k p
  refine ⟨η,hη,fun δ hδ hd => ?_⟩
  rw [cutoffMark,dif_pos hδ]
  apply mark_eq_of_test 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hδ k p ω
  rw [hEq δ hδ hd,UncutSmoothWords.test_eq_weight_normalized]
  rfl

/-- Actual mixed first-defect history mass converges as delta decreases
to zero, for every fixed smooth depth. -/
theorem mark_integral_tendsto (hΛ : 0≤Λ) (ν : Measure P) [IsFiniteMeasure ν] (k : ℕ) :
    Tendsto (fun δ : ℝ => ∫ q : History P k×Ω,CM δ k q.1 q.2 ∂(historyMeasure R ν k).prod μ)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ q : History P k×Ω,UM k q.1 q.2 ∂(historyMeasure R ν k).prod μ)) := by
  obtain ⟨K,hK,hKb⟩ := mark_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hΛ k
  apply DominatedCutoffLimit.integral_tendsto ((historyMeasure R ν k).prod μ)
    (W := fun q => UncutSmoothWords.weight L k q.1) (M := K)
    ((UncutHistoryMass.weight_integrable L ν k).comp_fst μ)
  · intro δ hδ
    have hh := MixedJointLevelData.mark_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (level L δ hδ 0 k)
    simpa only [cutoffMark,dif_pos hδ] using hh
  · intro δ hδ q
    rw [cutoff_mark_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hδ]
    by_cases hp : Active L δ k q.1
    · simpa only [hp,ite_true] using hKb q.1 q.2
    · simp only [hp,ite_false,norm_zero]
      exact mul_nonneg hK (UncutSmoothWords.weight_nonneg L k q.1)
  · intro q
    exact mark_eventually_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k q.1 q.2

end SHE.MixedJointUncutMark
