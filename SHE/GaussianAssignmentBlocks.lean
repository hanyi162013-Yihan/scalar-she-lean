module

public import SHE.GaussianFractionBaselines

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.GaussianAssignmentBlocks
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianVectorFractions
open scoped BigOperators
variable {E : Type*} [Zero E] {n m : ℕ}

def suppress (is : List (Fin n)) (x : Fin n → E) : Fin n → E :=
  match is with
  | [] => x
  | i :: is => suppress is (Function.update x i 0)

def block (choices : List (Fin n × Fin m)) (k : Fin m) : List (Fin n) :=
  choices.filterMap (fun p => if p.2 = k then some p.1 else none)

def suppressed (choices : List (Fin n × Fin m)) (k : Fin m) : List (Fin n) :=
  choices.filterMap (fun p => if k < p.2 then some p.1 else none)

def action (i : Fin n) (j k : Fin m) (F : (Fin n → E) → ℝ) : (Fin n → E) → ℝ :=
  if k < j then fun x => F (Function.update x i 0)
  else if k = j then fractionDifference i F else F

def factor (choices : List (Fin n × Fin m)) (k : Fin m)
    (F : (Fin n → E) → ℝ) : (Fin n → E) → ℝ :=
  choices.foldr (fun p G => action p.1 p.2 k G) F

theorem factor_cons (p : Fin n × Fin m) (choices : List (Fin n × Fin m))
    (k : Fin m) (F : (Fin n → E) → ℝ) :
    factor (p :: choices) k F = action p.1 p.2 k (factor choices k F) := rfl

theorem mem_suppressed (choices : List (Fin n × Fin m)) (k : Fin m) {i : Fin n}
    (hi : i ∈ suppressed choices k) : i ∈ choices.map Prod.fst := by
  obtain ⟨p, hp, he⟩ := List.mem_filterMap.mp hi
  split_ifs at he with h
  · have hh : p.1 = i := Option.some.inj he
    exact hh ▸ List.mem_map.mpr ⟨p, hp, rfl⟩

theorem suppress_update (is : List (Fin n)) (i : Fin n) (hi : i ∉ is) (x : Fin n → E) :
    suppress is (Function.update x i 0) = Function.update (suppress is x) i 0 := by
  induction is generalizing x with
  | nil => rfl
  | cons j is ih =>
    have hij : i ≠ j := fun h => hi (by simp [h])
    have hit : i ∉ is := fun h => hi (List.mem_cons_of_mem _ h)
    dsimp only [suppress]
    rw [Function.update_comm hij, ih hit]

/-- The ordered discrete Leibniz rule has a canonical form: one block of
differences for each assigned factor, evaluated with precisely the earlier
factors' foreign increments suppressed. The original vector tuple is kept. -/
theorem factor_eq_block (choices : List (Fin n × Fin m))
    (hnd : (choices.map Prod.fst).Nodup) (k : Fin m) (F : (Fin n → E) → ℝ)
    (x : Fin n → E) :
    factor choices k F x = fractionDifferences (block choices k) F (suppress (suppressed choices k) x) := by
  induction choices generalizing x with
  | nil => rfl
  | cons p choices ih =>
    obtain ⟨hi, hnd⟩ := List.nodup_cons.mp hnd
    have hnot : p.1 ∉ suppressed choices k := fun h => hi (mem_suppressed choices k h)
    by_cases hlt : k < p.2
    · rw [factor_cons]
      simp only [action, hlt, ite_true]
      rw [ih hnd]
      simp only [block, suppressed, List.filterMap_cons, hlt, ite_true, suppress]
      have hne : p.2 ≠ k := ne_of_gt hlt
      simp only [hne, ite_false]
    · by_cases heq : k = p.2
      · rw [factor_cons]
        simp only [action, if_neg hlt, if_pos heq, fractionDifference]
        rw [ih hnd, ih hnd, suppress_update _ _ hnot]
        simp only [block, suppressed, List.filterMap_cons, hlt, ite_false, heq, ite_true,
          lt_self_iff_false, fractionDifferences, List.foldr_cons, fractionDifference]
      · rw [factor_cons]
        simp only [action, if_neg hlt, if_neg heq]
        rw [ih hnd]
        simp only [block, suppressed, List.filterMap_cons, hlt, Ne.symm heq, ite_false]

def assignments (is : List (Fin n)) : List (List (Fin n × Fin m)) :=
  match is with
  | [] => [[]]
  | i :: is => (assignments is).flatMap (fun choices => List.ofFn (fun j : Fin m => (i, j) :: choices))

theorem assignment_coordinates (is : List (Fin n)) (choices : List (Fin n × Fin m))
    (hc : choices ∈ assignments (m := m) is) : choices.map Prod.fst = is := by
  induction is generalizing choices with
  | nil =>
    have he : choices = [] := by simpa only [assignments, List.mem_singleton] using hc
    subst choices
    rfl
  | cons i is ih =>
    obtain ⟨tail, ht, hj⟩ := List.mem_flatMap.mp hc
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hj
    subst choices
    simp only [List.map_cons, ih tail ht]

theorem action_eq_assigned (i : Fin n) (j k : Fin m)
    (F : Fin m → (Fin n → E) → ℝ) :
    action i j k (F k) = assignFractionFactor i F j k := by
  funext x
  rcases lt_trichotomy k j with h | h | h
  · simp only [action, h, ite_true, assignFractionFactor, ne_of_lt h, ite_false,
      not_lt_of_ge h.le, mul_one, one_mul]
  · subst k
    simp only [action, lt_self_iff_false, ite_false, ite_true, assignFractionFactor, mul_one, one_mul]
  · simp only [action, not_lt_of_ge h.le, ite_false, ne_of_gt h, assignFractionFactor,
      h, ite_true, one_mul, mul_one]

theorem families_eq_assignments (is : List (Fin n)) (F : Fin m → (Fin n → E) → ℝ) :
    fractionAssignmentFamilies is F =
      (assignments (m := m) is).map (fun choices k => factor choices k (F k)) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [fractionAssignmentFamilies, assignments, ih, List.flatMap_map, List.map_flatMap]
    apply congrArg (List.flatMap · (assignments (m := m) is))
    funext choices
    simp only [List.map_ofFn]
    congr 1
    funext j k x
    exact (congrFun (action_eq_assigned i j k (fun k => factor choices k (F k))) x).symm

/-- Exact all-order canonical root/rough block expansion, before any
Gaussian moment or positive heat-tree bound is applied. -/
theorem product_expansion (is : List (Fin n)) (hnd : is.Nodup)
    (F : Fin m → (Fin n → E) → ℝ) (x : Fin n → E) :
    fractionDifferences is (fun y => ∏ k, F k y) x =
      ((assignments (m := m) is).map (fun choices =>
        ∏ k, fractionDifferences (block choices k) (F k) (suppress (suppressed choices k) x))).sum := by
  rw [fractionDifferences_assignment_expansion, families_eq_assignments]
  simp only [sumProductFamilies, List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro choices hc
  apply Finset.prod_congr rfl
  intro k hk
  exact factor_eq_block choices ((assignment_coordinates is choices hc) ▸ hnd) k (F k) x

end SHE.GaussianAssignmentBlocks
