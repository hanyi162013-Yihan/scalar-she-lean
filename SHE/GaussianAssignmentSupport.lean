module

public import SHE.GaussianAssignmentBlocks

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.GaussianAssignmentBlocks
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianVectorFractions
open scoped BigOperators
variable {E : Type*} [Zero E] {n m : ℕ}

theorem mem_block_iff (choices : List (Fin n × Fin m)) (k : Fin m) (i : Fin n) :
    i ∈ block choices k ↔ (i, k) ∈ choices := by
  constructor
  · intro hi
    obtain ⟨p, hp, he⟩ := List.mem_filterMap.mp hi
    split_ifs at he with h
    have hh : p.1 = i := Option.some.inj he
    have hp' : p = (i, k) := Prod.ext hh h
    rw [← hp']
    exact hp
  · intro hi
    exact List.mem_filterMap.mpr ⟨(i, k), hi, by simp⟩

theorem block_mem_coordinates (choices : List (Fin n × Fin m)) (k : Fin m) {i : Fin n}
    (hi : i ∈ block choices k) : i ∈ choices.map Prod.fst :=
  List.mem_map.mpr ⟨(i, k), (mem_block_iff choices k i).mp hi, rfl⟩

theorem block_nodup (choices : List (Fin n × Fin m))
    (hnd : (choices.map Prod.fst).Nodup) (k : Fin m) : (block choices k).Nodup := by
  induction choices with
  | nil => exact List.nodup_nil
  | cons p choices ih =>
    obtain ⟨hi, hnd⟩ := List.nodup_cons.mp hnd
    by_cases hp : p.2 = k
    · simp only [block, List.filterMap_cons, hp, ite_true]
      exact List.nodup_cons.mpr ⟨(fun h => hi (block_mem_coordinates choices k h)), ih hnd⟩
    · simpa only [block, List.filterMap_cons, hp, ite_false] using ih hnd

theorem block_not_suppressed (choices : List (Fin n × Fin m))
    (hnd : (choices.map Prod.fst).Nodup) (k : Fin m) {i : Fin n}
    (hi : i ∈ block choices k) : i ∉ suppressed choices k := by
  intro hs
  have hib := (mem_block_iff choices k i).mp hi
  obtain ⟨p, hp, he⟩ := List.mem_filterMap.mp hs
  split_ifs at he with h
  have hh : p.1 = i := Option.some.inj he
  have hp' : p = (i, k) := List.inj_on_of_nodup_map hnd hp hib hh
  subst p
  exact (lt_irrefl k) h

theorem suppress_apply_of_not_mem (is : List (Fin n)) (i : Fin n) (hi : i ∉ is) (x : Fin n → E) :
    suppress is x i = x i := by
  induction is generalizing x with
  | nil => rfl
  | cons j is ih =>
    have hij : i ≠ j := fun h => hi (by simp [h])
    have hit : i ∉ is := fun h => hi (List.mem_cons_of_mem _ h)
    rw [suppress, ih hit, Function.update_of_ne hij]

/-- Every assigned Gaussian coordinate survives the foreign suppression
unchanged. Thus minimum-increment bounds use its genuine original law. -/
theorem suppress_assigned_coordinate (choices : List (Fin n × Fin m))
    (hnd : (choices.map Prod.fst).Nodup) (k : Fin m) {i : Fin n}
    (hi : i ∈ block choices k) (x : Fin n → E) :
    suppress (suppressed choices k) x i = x i :=
  suppress_apply_of_not_mem _ i (block_not_suppressed choices hnd k hi) x

section Measurable
variable [MeasurableSpace E]

theorem measurable_suppress (is : List (Fin n)) : Measurable (suppress (E := E) is) := by
  induction is with
  | nil => exact measurable_id
  | cons i is ih => exact ih.comp (by fun_prop)

def assignmentWord (choices : List (Fin n × Fin m))
    (F : Fin m → (Fin n → E) → ℝ) (x : Fin n → E) : ℝ :=
  ∏ k, fractionDifferences (block choices k) (F k) (suppress (suppressed choices k) x)

theorem measurable_assignmentWord (choices : List (Fin n × Fin m))
    (F : Fin m → (Fin n → E) → ℝ) (hF : ∀ k, Measurable (F k)) :
    Measurable (assignmentWord choices F) :=
  Finset.measurable_prod Finset.univ (fun k _ =>
    (measurable_fractionDifferences _ _ (hF k)).comp (measurable_suppress _))

theorem assignmentWord_bound (choices : List (Fin n × Fin m))
    (F : Fin m → (Fin n → E) → ℝ) (M : Fin m → ℝ) (hM : ∀ k, 0 ≤ M k)
    (hb : ∀ k x, |F k x| ≤ M k) (x : Fin n → E) :
    |assignmentWord choices F x| ≤ ∏ k, (2 : ℝ) ^ (block choices k).length * M k := by
  rw [assignmentWord, Finset.abs_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
    (fun k _ => fractionDifferences_bound _ _ (M k) (hb k) _)

theorem integrable_assignment_scores (μ : Fin n → Measure E) [∀ j, SigmaFinite (μ j)]
    (S : Fin n → E → ℝ) (hS : ∀ j, Integrable (S j) (μ j))
    (choices : List (Fin n × Fin m)) (F : Fin m → (Fin n → E) → ℝ)
    (hF : ∀ k, Measurable (F k)) (M : Fin m → ℝ) (hM : ∀ k, 0 ≤ M k)
    (hb : ∀ k x, |F k x| ≤ M k) :
    Integrable (fun x => (∏ j, S j (x j)) * assignmentWord choices F x) (Measure.pi μ) :=
  integrable_product_score_bounded μ S hS _ (measurable_assignmentWord choices F hF) _
    (assignmentWord_bound choices F M hM hb)

end Measurable

/-- Exact full-vector Gaussian score assignment into canonical root/rough
blocks, valid for singular covariances and all fixed finite orders. -/
theorem gaussian_product_identity {d : ℕ}
    (A : Fin n → MeasurableGeneralizedInverse.Mat d) (hA : ∀ j, (A j).PosSemidef)
    (direction : Fin n → State d)
    (hd : ∀ j, direction j ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (A j)).range)
    (is : List (Fin n)) (hnd : is.Nodup) (F : Fin m → (Fin n → State d) → ℝ)
    (hF : ∀ k, Measurable (F k)) (B : ℝ) (hB : ∀ x, |∏ k, F k x| ≤ B) :
    (∫ x, (∏ j, MeasurableGaussianScores.secondScore (A j) (direction j) (x j)) * (∏ k, F k x)
      ∂Measure.pi (fun j => multivariateGaussian 0 (A j))) =
      ∫ x, (∏ j, MeasurableGaussianScores.secondScore (A j) (direction j) (x j)) *
        ((assignments (m := m) is).map (fun choices => assignmentWord choices F x)).sum
        ∂Measure.pi (fun j => multivariateGaussian 0 (A j)) := by
  rw [← gaussian_vector_scores_center_all A hA direction hd is (fun x => ∏ k, F k x) (by fun_prop) B hB]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  dsimp only
  rw [product_expansion is hnd]
  rfl

end SHE.GaussianAssignmentBlocks
