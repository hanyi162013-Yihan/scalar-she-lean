module

public import SHEStochastic.DirectionalJetPartitions

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.DirectionalJets
variable {E : Type*}

/-- Every assignment keeps each perturbation direction exactly once. -/
theorem pairs_product (w : List E) (g : E → ℝ) (p : List E × List E) (hp : p∈pairs w) :
    (p.1.map g).prod*(p.2.map g).prod = (w.map g).prod := by
  induction w generalizing p with
  | nil =>
    change p∈[([],[])] at hp
    have he := List.mem_singleton.mp hp
    subst p
    simp
  | cons v w ih =>
    rcases List.mem_append.mp hp with h | h
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
      have hh := ih q hq
      simp only [List.map_cons, List.prod_cons]
      rw [mul_assoc, hh]
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
      have hh := ih q hq
      simp only [List.map_cons, List.prod_cons]
      calc
        _ = g v*((q.1.map g).prod*(q.2.map g).prod) := by ring
        _ = _ := by rw [hh]

theorem pairs_count (w : List E) : (pairs w).length=2^w.length := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    simp only [pairs, List.length_append, List.length_map, List.length_cons, ih, pow_succ]
    omega

theorem proper_count (w : List E) : (properPairs w).length ≤ 2^w.length := by
  rw [← pairs_count]
  exact List.length_filter_le _ _

end SHEStochastic.DirectionalJets
