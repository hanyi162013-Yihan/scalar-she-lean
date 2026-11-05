module

public import SHE.JointUncutWordEvaluation
public import SHE.DominatedCutoffLimit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.JointUncutEvaluationLimit
open Set MeasureTheory Filter Topology StoppedFourier WordRecursion
open CutoffWordLevel CutoffWordHistories CutoffCarriers CutoffUncutComparison
open JointUncutWordEvaluation
open Classical
local instance jointUncutEvaluationLimit_sigma : MeasurableSpace CircleL2 := borel _
local instance jointUncutEvaluationLimit_borel : BorelSpace CircleL2 := ⟨rfl⟩
variable {P Ω : Type} [MeasurableSpace P] [MeasurableSpace Ω] {R : ReferenceData} {n : ℕ}
variable (L : Level R P n) (Λ : ℝ)
variable (U V : Ω×ℝ→CircleL2) (XU XV : Ω×(ℝ×HeatCircle)→ℝ)

def cutoffLeaf (δ : ℝ) (k : ℕ) (p : History P k) (ω : Ω) : ℝ :=
  if hδ : 0<δ then JointWordAnalytic.leaf (RecursiveHeatBounds.level L δ hδ 0 k) Λ U V XU XV p ω else 0

def cutoffReference (δ : ℝ) (k : ℕ) (p : History P k) (ω : Ω) : ℝ :=
  if hδ : 0<δ then JointWordAnalytic.reference (RecursiveHeatBounds.level L δ hδ 0 k) Λ U V XU XV p ω else 0

theorem leaf_eventually_eq (k : ℕ) (p : History P k) (ω : Ω) :
    ∃ η : ℝ,0<η ∧ ∀ δ>0,δ<η→cutoffLeaf L Λ U V XU XV δ k p ω=
      JointUncutWordEvaluation.leaf L Λ U V XU XV k p ω := by
  obtain ⟨η,hη,hEq⟩ := eventually_test_eq L k p
  refine ⟨η,hη,fun δ hδ hd => ?_⟩
  rw [cutoffLeaf,dif_pos hδ]
  unfold JointWordAnalytic.leaf JointWordAnalytic.state
  rw [hEq δ hδ hd,observations_eq L hδ zero_lt_one k p,terminal_eq L hδ zero_lt_one k p]
  rfl

theorem reference_eventually_eq (k : ℕ) (p : History P k) (ω : Ω) :
    ∃ η : ℝ,0<η ∧ ∀ δ>0,δ<η→cutoffReference L Λ U V XU XV δ k p ω=
      JointUncutWordEvaluation.reference L Λ U V XU XV k p ω := by
  obtain ⟨η,hη,hEq⟩ := eventually_test_eq L k p
  refine ⟨η,hη,fun δ hδ hd => ?_⟩
  rw [cutoffReference,dif_pos hδ,JointRecursiveReferenceLimit.reference_eq_average L δ hδ Λ U V XU XV 0 k p ω,
    nodeCovariance_eq L hδ zero_lt_one k (p,(R.base,0)),hEq δ hδ hd]
  unfold JointWordAnalytic.state
  rw [observations_eq L hδ zero_lt_one k p]
  rfl

/-- The actual recursively moving joint leaf admits the full time-gap
cutoff limit. Domination retains the proved integrable uncut history
weight, rather than a delta-dependent uniform derivative constant. -/
theorem leaf_integral_tendsto (hU : Measurable U) (hV : Measurable V)
    (hXU : Measurable XU) (hXV : Measurable XV)
    (ν : Measure P) [IsFiniteMeasure ν] (τ : Measure Ω) [IsFiniteMeasure τ] (k : ℕ) :
    Tendsto (fun δ : ℝ => ∫ q : History P k×Ω,cutoffLeaf L Λ U V XU XV δ k q.1 q.2
      ∂(historyMeasure R ν k).prod τ) (𝓝[>] (0:ℝ))
      (𝓝 (∫ q : History P k×Ω,JointUncutWordEvaluation.leaf L Λ U V XU XV k q.1 q.2
        ∂(historyMeasure R ν k).prod τ)) := by
  obtain ⟨M,hMn,hM,_⟩ := evaluation_norm_bounds L Λ U V XU XV k
  apply DominatedCutoffLimit.integral_tendsto ((historyMeasure R ν k).prod τ)
    (W := fun q => UncutSmoothWords.weight L k q.1) (M := M)
    ((UncutHistoryMass.weight_integrable L ν k).comp_fst τ)
  · intro δ hδ
    have hh := JointWordAnalytic.leaf_measurable (RecursiveHeatBounds.level L δ hδ 0 k) Λ hU hV hXU hXV
    simpa only [cutoffLeaf,dif_pos hδ] using hh
  · intro δ hδ q
    rw [cutoffLeaf,dif_pos hδ,cutoff_leaf_eq L Λ U V XU XV hδ k q.1 q.2]
    by_cases hp : Active L δ k q.1
    · simpa only [hp,ite_true] using hM q.1 q.2
    · simp only [hp,ite_false,norm_zero]
      exact mul_nonneg hMn (UncutSmoothWords.weight_nonneg L k q.1)
  · intro q
    exact leaf_eventually_eq L Λ U V XU XV k q.1 q.2

theorem reference_integral_tendsto (hU : Measurable U) (hV : Measurable V)
    (hXU : Measurable XU) (hXV : Measurable XV)
    (ν : Measure P) [IsFiniteMeasure ν] (τ : Measure Ω) [IsFiniteMeasure τ] (k : ℕ) :
    Tendsto (fun δ : ℝ => ∫ q : History P k×Ω,cutoffReference L Λ U V XU XV δ k q.1 q.2
      ∂(historyMeasure R ν k).prod τ) (𝓝[>] (0:ℝ))
      (𝓝 (∫ q : History P k×Ω,JointUncutWordEvaluation.reference L Λ U V XU XV k q.1 q.2
        ∂(historyMeasure R ν k).prod τ)) := by
  obtain ⟨M,hMn,_,hM⟩ := evaluation_norm_bounds L Λ U V XU XV k
  apply DominatedCutoffLimit.integral_tendsto ((historyMeasure R ν k).prod τ)
    (W := fun q => UncutSmoothWords.weight L k q.1) (M := M)
    ((UncutHistoryMass.weight_integrable L ν k).comp_fst τ)
  · intro δ hδ
    have hh := JointWordAnalytic.reference_measurable (RecursiveHeatBounds.level L δ hδ 0 k) Λ hU hV hXU hXV
    simpa only [cutoffReference,dif_pos hδ] using hh
  · intro δ hδ q
    rw [cutoffReference,dif_pos hδ,cutoff_reference_eq L Λ U V XU XV hδ k q.1 q.2]
    by_cases hp : Active L δ k q.1
    · simpa only [hp,ite_true] using hM q.1 q.2
    · simp only [hp,ite_false,norm_zero]
      exact mul_nonneg hMn (UncutSmoothWords.weight_nonneg L k q.1)
  · intro q
    exact reference_eventually_eq L Λ U V XU XV k q.1 q.2

end SHE.JointUncutEvaluationLimit
