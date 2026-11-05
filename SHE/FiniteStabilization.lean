module

public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace SHE.FiniteStabilization
open Finset

/-- A finite-threshold construction can dominate any prescribed next
analytic separation requirement, regardless of monotonicity of that
requirement. -/
def thresholds (F : ℝ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => max (thresholds F n+1) (F (thresholds F n))

theorem thresholds_strictMono (F : ℝ → ℝ) : StrictMono (thresholds F) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact lt_of_lt_of_le (by linarith : thresholds F n < thresholds F n+1) (le_max_left _ _)

theorem thresholds_ge_one (F : ℝ → ℝ) (n : ℕ) : 1 ≤ thresholds F n :=
  (thresholds_strictMono F).monotone (Nat.zero_le n)

theorem thresholds_dominate (F : ℝ → ℝ) (n : ℕ) :
    F (thresholds F n) ≤ thresholds F (n+1) := le_max_right _ _

/-- An increasing family of subsets of a finite set must have an
adjacent equality within the cardinality bound. -/
theorem monotone_finset_stabilizes {I : Type*} [Fintype I]
    (s : ℕ → Finset I) (hs : Monotone s) :
    ∃ k ≤ Fintype.card I, s k = s (k+1) := by
  by_contra h
  push Not at h
  have hcard : ∀ k ≤ Fintype.card I+1, k ≤ (s k).card := by
    intro k
    induction k with
    | zero => exact fun _ => Nat.zero_le _
    | succ k ih =>
      intro hk
      have hkN : k ≤ Fintype.card I := by omega
      have hstrict : s k ⊂ s (k+1) :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hs (Nat.le_succ k),h k hkN⟩
      have hh := Finset.card_lt_card hstrict
      have hp := ih (by omega)
      omega
  have hh := hcard (Fintype.card I+1) le_rfl
  have hu := Finset.card_le_univ (s (Fintype.card I+1))
  omega

/-- The same finite principle with an explicit ambient bound, useful
when a family is represented by a finite collection of relation pairs. -/
theorem monotone_finset_stabilizes_card {I : Type*} (s : ℕ → Finset I)
    (hs : Monotone s) (N : ℕ) (hN : ∀ k, (s k).card ≤ N) :
    ∃ k ≤ N, s k = s (k+1) := by
  by_contra h
  push Not at h
  have hcard : ∀ k ≤ N+1, k ≤ (s k).card := by
    intro k
    induction k with
    | zero => exact fun _ => Nat.zero_le _
    | succ k ih =>
      intro hk
      have hkN : k ≤ N := by omega
      have hstrict : s k ⊂ s (k+1) :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hs (Nat.le_succ k),h k hkN⟩
      have hh := Finset.card_lt_card hstrict
      have hp := ih (by omega)
      omega
  have hh := hcard (N+1) le_rfl
  have hu := hN (N+1)
  omega

/-- A monotone sequence of finite-index binary relations has two
identical adjacent relations within `|I|²+1` threshold tests. This also
applies to the connected-component equivalence relations of increasing
coherence graphs. -/
theorem monotone_relation_stabilizes {I : Type*} [Fintype I]
    (r : ℕ → I → I → Prop)
    (hr : ∀ i j, Monotone (fun k => r k i j)) :
    ∃ k ≤ (Fintype.card I)^2, ∀ i j, r k i j ↔ r (k+1) i j := by
  classical
  let s : ℕ → Finset (I × I) := fun k => univ.filter (fun p => r k p.1 p.2)
  have hs : Monotone s := by
    intro k l hkl p hp
    simpa only [s,mem_filter,mem_univ,true_and] using hr p.1 p.2 hkl
      (by simpa only [s,mem_filter,mem_univ,true_and] using hp)
  obtain ⟨k,hk,he⟩ := monotone_finset_stabilizes s hs
  refine ⟨k,by simpa only [Fintype.card_prod,pow_two] using hk,fun i j => ?_⟩
  have hh := congrArg (fun z : Finset (I × I) => (i,j) ∈ z) he
  simpa only [s,mem_filter,mem_univ,true_and,eq_iff_iff] using hh

end SHE.FiniteStabilization
