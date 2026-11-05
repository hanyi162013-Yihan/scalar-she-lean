module

public import SHE.UncutSmoothWords

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.CutoffUncutComparison
open Set MeasureTheory Filter StoppedFourier WordRecursion
open CutoffWordLevel CutoffWordHistories CutoffCarriers CutoffInsertionCore GaussianConvolution
open NormalizedInsertion
open Classical
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

def Active (δ : ℝ) : (k : ℕ) → History P k → Prop
  | 0 => fun _ => True
  | k+1 => fun p => Active δ k p.1 ∧ (carrier L k).Good δ p

theorem active_measurableSet (δ : ℝ) (k : ℕ) : MeasurableSet {p | Active L δ k p} := by
  induction k with
  | zero => exact MeasurableSet.univ
  | succ k ih => exact (measurable_fst ih).inter ((carrier L k).good_measurableSet δ)

theorem core_zero_test {m : ℕ} (a : ℝ→ℝ) (c : ℝ) (r : WordRecursion.State m) :
    core a c r (0 : WordRecursion.State m→ℝ)=0 := by
  have hh := core_smul_test a c 0 r (0 : WordRecursion.State m→ℝ)
  simpa only [zero_smul] using hh

theorem cutoffRow_eq_row {δ : ℝ} (hδ : 0<δ) (k : ℕ)
    (p : History P k × (ℝ×HeatCircle)) (hp : (carrier L k).Good δ p) :
    (carrier L k).cutoffRow δ p=row L k p := by
  have hi : Interior L k p := (carrier L k).good_time hδ hp
  simp only [Level.cutoffRow,hp,ite_true,row,hi]

/-- Every cutoff word is an exact restriction of the same uncut word,
rather than a family with unrelated derivative bounds. -/
theorem test_eq_active {δ : ℝ} (hδ : 0<δ) (k : ℕ) (p : History P k) :
    (RecursiveHeatBounds.level L δ hδ 0 k).test p=
      if Active L δ k p then UncutSmoothWords.test L k p else 0 := by
  induction k with
  | zero => simp only [Active,ite_true]; rfl
  | succ k ih =>
    change History P k × (ℝ×HeatCircle) at p
    rw [CutoffCarriers.test_succ L hδ k p,ih p.1]
    by_cases ha : Active L δ k p.1
    · simp only [ha,ite_true]
      by_cases hg : (carrier L k).Good δ p
      · rw [cutoffRow_eq_row L hδ k p hg]
        simp only [Active,ha,hg,true_and,ite_true]
        rfl
      · simp only [Level.cutoffRow,hg,ite_false,core_zero,Active,ha,true_and]
    · simp only [ha,ite_false]
      have hz : gaussianAverage ((carrier L k).nodeCovariance p).val
          (0 : WordRecursion.State (n+k)→ℝ)=0 := by
        funext z
        exact integral_zero _ _
      rw [hz,core_zero_test]
      simp only [Active,ha,false_and,ite_false]

theorem test_norm_bound (k : ℕ) : ∃ M : ℝ, 0≤M ∧
    ∀ (δ : ℝ) (hδ : 0<δ) p z,
      ‖(RecursiveHeatBounds.level L δ hδ 0 k).test p z‖≤M*UncutSmoothWords.weight L k p := by
  obtain ⟨M,hMn,hM⟩ := UncutSmoothWords.test_norm_bound L k
  refine ⟨M,hMn,fun δ hδ p z => ?_⟩
  rw [test_eq_active L hδ k p]
  by_cases hp : Active L δ k p
  · simpa only [hp,ite_true] using hM p z
  · simp only [hp,ite_false,Pi.zero_apply,norm_zero]
    exact mul_nonneg hMn (UncutSmoothWords.weight_nonneg L k p)

/-- For each actual finite history the cutoff is eventually immaterial.
The threshold is history dependent, and no uniform positive gap is asserted. -/
theorem eventually_test_eq (k : ℕ) (p : History P k) :
    ∃ η : ℝ, 0<η ∧ ∀ (δ : ℝ) (hδ : 0<δ), δ<η →
      (RecursiveHeatBounds.level L δ hδ 0 k).test p=UncutSmoothWords.test L k p := by
  induction k with
  | zero => exact ⟨1,zero_lt_one,fun _ _ _ => rfl⟩
  | succ k ih =>
    change History P k × (ℝ×HeatCircle) at p
    obtain ⟨η,hη,hEq⟩ := ih p.1
    by_cases hi : Interior L k p
    · refine ⟨min η ((carrier L k).terminal p.1-p.2.1),lt_min hη (sub_pos.mpr hi.2),?_⟩
      intro δ hδ hd
      have hg : (carrier L k).Good δ p := ⟨hi.1,by linarith [hd.trans_le (min_le_right η _) ]⟩
      rw [CutoffCarriers.test_succ L hδ k p,hEq δ hδ (hd.trans_le (min_le_left _ _)),
        cutoffRow_eq_row L hδ k p hg]
      rfl
    · refine ⟨η,hη,fun δ hδ hd => ?_⟩
      have hg : ¬(carrier L k).Good δ p := fun h => hi ((carrier L k).good_time hδ h)
      rw [CutoffCarriers.test_succ L hδ k p]
      simp only [Level.cutoffRow,hg,ite_false,core_zero,UncutSmoothWords.test,row,hi]

end SHE.CutoffUncutComparison
