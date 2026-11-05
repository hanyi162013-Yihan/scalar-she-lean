module

public import SHE.WeightedHistoryL2Limit
public import SHE.JointLocalTestScaling
public import SHE.JointUncutEvaluationLimit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace SHE.JointUncutLocalRemainder
open Set Filter MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open JointUncutEvaluationLimit JointUncutWordEvaluation Topology
local instance : MeasurableSpace CircleL2:=borel _
local instance : BorelSpace CircleL2:=⟨rfl⟩
variable {P Ω:Type} [MeasurableSpace P] [MeasurableSpace Ω]
variable {R:ReferenceData} {n:ℕ} (L:Level R P n) (Λ:ℝ)
variable (U V:Ω×ℝ→CircleL2) (XU XV:Ω×(ℝ×HeatCircle)→ℝ)
variable (hU:Measurable U) (hV:Measurable V) (hXU:Measurable XU) (hXV:Measurable XV)
variable (ν:Measure P) [IsFiniteMeasure ν] (τ:Measure Ω) [IsProbabilityMeasure τ]


open CutoffCarriers CutoffUncutComparison UncutWordEvaluation Classical

def value (k:ℕ) (p:History P k) (ω:Ω):ℝ:=
  UncutSmoothWords.weight L k p*JointWordAnalytic.remainder (normalizedLevel L k) Λ U V XU XV p ω

def cutoff (δ:ℝ) (k:ℕ) (p:History P k) (ω:Ω):ℝ:=
  if hδ:0<δ then JointWordAnalytic.remainder (RecursiveHeatBounds.level L δ hδ 0 k) Λ U V XU XV p ω else 0

theorem cutoff_eq {δ:ℝ} (hδ:0<δ) (k:ℕ) (p:History P k) (ω:Ω):
    cutoff L Λ U V XU XV δ k p ω=if Active L δ k p then value L Λ U V XU XV k p ω else 0:=by
  rw [cutoff,dite_eq_left hδ]
  by_cases hp:Active L δ k p
  · rw [if_pos hp]
    apply JointLocalTestScaling.remainder_smul (RecursiveHeatBounds.level L δ hδ 0 k)
      (normalizedLevel L k) Λ U V XU XV (UncutSmoothWords.weight L k p) p ω
      (observations_eq L hδ zero_lt_one k p) (CutoffCarriers.terminal_eq L hδ zero_lt_one k p)
    rw [test_eq_active L hδ k p,if_pos hp,UncutSmoothWords.test_eq_weight_normalized]
    rfl
  · rw [if_neg hp]
    have he:=JointLocalTestScaling.remainder_smul (RecursiveHeatBounds.level L δ hδ 0 k)
      (normalizedLevel L k) Λ U V XU XV 0 p ω
      (observations_eq L hδ zero_lt_one k p) (CutoffCarriers.terminal_eq L hδ zero_lt_one k p)
      (by rw [test_eq_active L hδ k p,if_neg hp,zero_smul])
    simpa only [zero_mul] using he

theorem bound (k:ℕ):∃C:ℝ,0≤C ∧ ∀p ω,‖value L Λ U V XU XV k p ω‖≤C*UncutSmoothWords.weight L k p:=by
  obtain ⟨C,hC,hCb⟩:=JointInsertionBounds.uniform_level_bound (normalizedLevel L k) Λ U V XU XV
  refine ⟨C,hC,fun p ω=>?_⟩
  rw [value,norm_mul,Real.norm_eq_abs,abs_of_nonneg (UncutSmoothWords.weight_nonneg L k p)]
  exact (mul_le_mul_of_nonneg_left (hCb p ω).2.2 (UncutSmoothWords.weight_nonneg L k p)).trans_eq (mul_comm _ _)

include hU hV hXU hXV in
/-- The whole actual local time/space remainder has a strong uncut
history-averaged limit, with the original integrable history weight. -/
theorem averaged_limit (k:ℕ):
    let E:=fun δ:ℝ=>fun ω=>∫p,cutoff L Λ U V XU XV δ k p ω-value L Λ U V XU XV k p ω ∂historyMeasure R ν k
    (∀δ,Integrable (fun ω=>‖E δ ω‖^2) τ) ∧
      Tendsto (fun δ=>∫ω,‖E δ ω‖^2 ∂τ) (𝓝[>] (0:ℝ)) (𝓝 0):=by
  obtain ⟨C,hC,hCb⟩:=bound L Λ U V XU XV k
  let W:=UncutSmoothWords.weight L k
  have hW:Integrable W (historyMeasure R ν k):=UncutHistoryMass.weight_integrable L ν k
  have hm:Measurable (fun z:History P k×Ω=>value L Λ U V XU XV k z.1 z.2):=
    ((UncutSmoothWords.weight_measurable L k).comp measurable_fst).mul
      (JointWordAnalytic.remainder_measurable (normalizedLevel L k) Λ hU hV hXU hXV)
  have hfm(δ:ℝ):Measurable (fun z:History P k×Ω=>cutoff L Λ U V XU XV δ k z.1 z.2):=by
    by_cases hδ:0<δ
    · simpa only [cutoff,dite_eq_left hδ] using
        JointWordAnalytic.remainder_measurable (RecursiveHeatBounds.level L δ hδ 0 k) Λ hU hV hXU hXV
    · simp only [cutoff,dite_eq_right hδ]
      exact measurable_const
  have hb(δ:ℝ)(p:History P k)(ω:Ω):‖cutoff L Λ U V XU XV δ k p ω‖≤C*W p:=by
    by_cases hδ:0<δ
    · rw [cutoff_eq L Λ U V XU XV hδ]
      split_ifs
      · exact hCb p ω
      · exact (norm_zero).le.trans (mul_nonneg hC (UncutSmoothWords.weight_nonneg L k p))
    · rw [cutoff,dite_eq_right hδ,norm_zero]
      exact mul_nonneg hC (UncutSmoothWords.weight_nonneg L k p)
  have he(z:History P k×Ω):∃η:ℝ,0<η ∧ ∀δ>0,δ<η→
      cutoff L Λ U V XU XV δ k z.1 z.2=value L Λ U V XU XV k z.1 z.2:=by
    obtain ⟨η,hη,hEq⟩:=eventually_test_eq L k z.1
    refine ⟨η,hη,fun δ hδ hd=>?_⟩
    rw [cutoff,dite_eq_left hδ]
    apply JointLocalTestScaling.remainder_smul (RecursiveHeatBounds.level L δ hδ 0 k)
      (normalizedLevel L k) Λ U V XU XV (UncutSmoothWords.weight L k z.1) z.1 z.2
      (observations_eq L hδ zero_lt_one k z.1) (CutoffCarriers.terminal_eq L hδ zero_lt_one k z.1)
    rw [hEq δ hδ hd,UncutSmoothWords.test_eq_weight_normalized]
    rfl
  have ht:=DominatedCutoffLimit.integral_abs_sub_tendsto_zero ((historyMeasure R ν k).prod τ)
    (W:=fun z=>W z.1) (M:=C) (hW.comp_fst τ) hm (fun δ _=>hfm δ)
    (fun z=>hCb z.1 z.2) (fun δ _ z=>hb δ z.1 z.2) he
  exact WeightedHistoryL2Limit.averaged_limit (historyMeasure R ν k) τ
    (fun δ:ℝ=>fun z=>cutoff L Λ U V XU XV δ k z.1 z.2)
    (fun z=>value L Λ U V XU XV k z.1 z.2) hfm hm W hW
    (UncutSmoothWords.weight_nonneg L k) hC hb hCb (𝓝[>] (0:ℝ))
    (by simpa only [Real.norm_eq_abs] using ht)

end SHE.JointUncutLocalRemainder
