module

public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE
open Filter Topology

/-- At any deterministic damping sequence, all finitely many error
families can be made smaller than any prescribed positive tolerance
along one strictly increasing deterministic approximation diagonal.
This applies simultaneously to both prescribed weak laws. -/
theorem common_approximation_diagonal {I : Type*} (s : Finset I)
    (err : I → ℕ → ℝ → ℝ) (damp tolerance : ℕ → ℝ)
    (htolerance : ∀ k, 0 < tolerance k)
    (hlim : ∀ k i, i ∈ s → Tendsto (fun n => err i n (damp k)) atTop (𝓝 0)) :
    ∃ index : ℕ → ℕ, StrictMono index ∧
      ∀ k i, i ∈ s → |err i (index k) (damp k)| < tolerance k := by
  have htail : ∀ k, ∀ᶠ n in atTop, ∀ i ∈ s, |err i n (damp k)| < tolerance k := by
    intro k
    rw [eventually_all_finset]
    intro i hi
    have habs : Tendsto (fun n => |err i n (damp k)|) atTop (𝓝 0) := by simpa using (hlim k i hi).abs
    exact habs.eventually (gt_mem_nhds (htolerance k))
  choose N hN using fun k => eventually_atTop.mp (htail k)
  let index : ℕ → ℕ := Nat.rec (N 0) (fun k prev => max (N (k+1)) (prev+1))
  have hmajor : ∀ k, N k ≤ index k := by
    intro k
    cases k with
    | zero => exact le_rfl
    | succ k => exact le_max_left _ _
  have hstep : ∀ k, index k < index (k+1) := by
    intro k
    exact lt_of_lt_of_le (Nat.lt_succ_self (index k)) (le_max_right _ _)
  exact ⟨index, strictMono_nat_of_lt_succ hstep, fun k i hi => hN k (index k) (hmajor k) i hi⟩

/-- The common index also tends to infinity, so any independently
required approximation limit remains valid on that diagonal. -/
theorem common_approximation_diagonal_tendsto {I : Type*} (s : Finset I)
    (err : I → ℕ → ℝ → ℝ) (damp tolerance : ℕ → ℝ)
    (htolerance : ∀ k, 0 < tolerance k)
    (hlim : ∀ k i, i ∈ s → Tendsto (fun n => err i n (damp k)) atTop (𝓝 0)) :
    ∃ index : ℕ → ℕ, StrictMono index ∧ Tendsto index atTop atTop ∧
      ∀ k i, i ∈ s → |err i (index k) (damp k)| < tolerance k := by
  obtain ⟨index,hi,herr⟩ := common_approximation_diagonal s err damp tolerance htolerance hlim
  exact ⟨index,hi,hi.tendsto_atTop,herr⟩

end SHE
