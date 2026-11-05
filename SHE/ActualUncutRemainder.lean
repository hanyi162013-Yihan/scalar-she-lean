module
public import SHE.DominatedCutoffLimit
public import SHE.ActualVarianceScaling
public import SHE.ActualRecursiveRemainder
public import SHE.UncutWordEvaluation
public import SHE.WeightedHistoryL2Limit

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.ActualUncutRemainder
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers CutoffUncutComparison UncutWordEvaluation IntegratedPhysicalStep
  Filter Topology
open scoped NNReal
open Classical
local instance actualUncutRemainder_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance actualUncutRemainder_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
variable {P Ω:Type}[MeasurableSpace P][MeasurableSpace Ω]
variable {R:ReferenceData}{n:ℕ}(L:Level R P n)
variable (a:ℝ→ℝ)(ha:Measurable a){A:ℝ}(hAn:0≤A)(hA:∀z,|a z|≤A)
variable (U:Ω×ℝ→CircleL2)(X:Ω×(ℝ×HeatCircle)→ℝ)

def value (k:ℕ)(p:History P k)(ω:Ω):ℝ:=
  UncutSmoothWords.weight L k p*PhysicalIto.wordRemainder ((normalizedLevel L k).window p) a
    (fun t=>U (ω,t)) (fun q=>X (ω,q)) ((normalizedLevel L k).test p)

def cutoff (δ:ℝ)(k:ℕ)(p:History P k)(ω:Ω):ℝ:=
  if hδ:0<δ then ActualRecursiveRemainder.remainder L δ hδ a U X 0 k p ω else 0

theorem cutoff_eq {δ:ℝ}(hδ:0<δ)(k:ℕ)(p:History P k)(ω:Ω):
    cutoff L a U X δ k p ω=if Active L δ k p then value L a U X k p ω else 0:=by
  rw [cutoff,dif_pos hδ]
  by_cases hp:Active L δ k p
  · rw [if_pos hp]
    exact ActualVarianceScaling.remainder_smul (RecursiveHeatBounds.level L δ hδ 0 k)
      (normalizedLevel L k) a U X (UncutSmoothWords.weight L k p) p ω
      (observations_eq L hδ zero_lt_one k p) (CutoffCarriers.terminal_eq L hδ zero_lt_one k p)
      (by rw [test_eq_active L hδ k p,if_pos hp,UncutSmoothWords.test_eq_weight_normalized];rfl)
  · rw [if_neg hp]
    have he:=ActualVarianceScaling.remainder_smul (RecursiveHeatBounds.level L δ hδ 0 k)
      (normalizedLevel L k) a U X 0 p ω
      (observations_eq L hδ zero_lt_one k p) (CutoffCarriers.terminal_eq L hδ zero_lt_one k p)
      (by rw [test_eq_active L hδ k p,if_neg hp,zero_smul])
    simpa only [zero_mul,ActualRecursiveRemainder.remainder] using he

include ha hAn hA in
theorem bound (hU:Measurable U)(hX:Measurable X)(k:ℕ):
    ∃C:ℝ,0≤C∧∀p ω,‖value L a U X k p ω‖≤C*UncutSmoothWords.weight L k p:=by
  let D:=ActualVarianceLevel.data (normalizedLevel L k) a U X (fun _ _ _=>0)
  have hD:=ActualVarianceLevel.analyticConditions (normalizedLevel L k) a ha U hU X hX (fun _ _ _=>0) hAn hA
  obtain ⟨C,hC,hCb⟩:=uniform_level_bound D hD
  refine ⟨C,hC,fun p ω=>?_⟩
  rw [value,norm_mul,Real.norm_eq_abs,abs_of_nonneg (UncutSmoothWords.weight_nonneg L k p)]
  exact (mul_le_mul_of_nonneg_left (hCb p ω).2.2.1 (UncutSmoothWords.weight_nonneg L k p)).trans_eq (mul_comm _ _)

include ha in
theorem value_measurable (hU:Measurable U)(hX:Measurable X)(k:ℕ):
    Measurable (fun z:History P k×Ω=>value L a U X k z.1 z.2):=
  ((UncutSmoothWords.weight_measurable L k).comp measurable_fst).mul
    (ActualVarianceLevel.remainder_measurable (normalizedLevel L k) a ha U hU X hX (fun _ _ _=>0))

include ha in
theorem cutoff_measurable (hU:Measurable U)(hX:Measurable X)(δ:ℝ)(k:ℕ):
    Measurable (fun z:History P k×Ω=>cutoff L a U X δ k z.1 z.2):=by
  by_cases hδ:0<δ
  · simpa only [cutoff,dif_pos hδ,ActualRecursiveRemainder.remainder,ActualVarianceLevel.data,
      IntegratedPhysicalStep.LevelData.remainder] using
      ActualVarianceLevel.remainder_measurable (RecursiveHeatBounds.level L δ hδ 0 k) a ha U hU X hX (fun _ _ _=>0)
  · simp only [cutoff,dif_neg hδ]
    exact measurable_const

theorem eventually_eq (k:ℕ)(p:History P k)(ω:Ω):
    ∃η:ℝ,0<η∧∀δ>0,δ<η→cutoff L a U X δ k p ω=value L a U X k p ω:=by
  obtain ⟨η,hη,hEq⟩:=eventually_test_eq L k p
  refine ⟨η,hη,fun δ hδ hd=>?_⟩
  rw [cutoff,dif_pos hδ]
  exact ActualVarianceScaling.remainder_smul (RecursiveHeatBounds.level L δ hδ 0 k)
    (normalizedLevel L k) a U X (UncutSmoothWords.weight L k p) p ω
    (observations_eq L hδ zero_lt_one k p) (CutoffCarriers.terminal_eq L hδ zero_lt_one k p)
    (by rw [hEq δ hδ hd,UncutSmoothWords.test_eq_weight_normalized];rfl)

include ha hAn hA in
/-- All recursive time cutoffs are removed with the original integrable
history weight, for the actual bounded measurable bracket coefficient. -/
theorem integral_tendsto (hU:Measurable U)(hX:Measurable X)
    (ν:Measure P)[IsFiniteMeasure ν](μ:Measure Ω)[IsFiniteMeasure μ](k:ℕ):
    Tendsto (fun δ=>∫z:History P k×Ω,cutoff L a U X δ k z.1 z.2 ∂(historyMeasure R ν k).prod μ)
      (𝓝[>] (0:ℝ)) (𝓝 (∫z:History P k×Ω,value L a U X k z.1 z.2 ∂(historyMeasure R ν k).prod μ)):=by
  obtain ⟨C,hC,hCb⟩:=bound L a ha hAn hA U X hU hX k
  apply DominatedCutoffLimit.integral_tendsto ((historyMeasure R ν k).prod μ)
    (W:=fun z=>UncutSmoothWords.weight L k z.1) (M:=C)
    ((UncutHistoryMass.weight_integrable L ν k).comp_fst μ)
  · intro δ hδ
    exact cutoff_measurable L a ha U X hU hX δ k
  · intro δ hδ z
    rw [cutoff_eq L a U X hδ]
    split_ifs
    · exact hCb z.1 z.2
    · exact (norm_zero).le.trans (mul_nonneg hC (UncutSmoothWords.weight_nonneg L k z.1))
  · intro z
    exact eventually_eq L a U X k z.1 z.2

end SHE.ActualUncutRemainder
