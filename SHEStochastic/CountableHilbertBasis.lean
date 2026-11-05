module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Topology.Bases
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic
open Set Metric TopologicalSpace

variable {κ E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [SeparableSpace E]

/-- Orthogonal unit vectors have disjoint small balls, hence there are
only countably many in a separable Hilbert space. -/
theorem hilbertBasis_countable (b : HilbertBasis κ ℝ E) : Countable κ := by
  have hd : Pairwise (fun i j => Disjoint (ball (b i) (1 / 4)) (ball (b j) (1 / 4))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hsq : dist (b i) (b j) ^ 2 = 2 := by
      rw [dist_eq_norm, norm_sub_sq_real, b.orthonormal.inner_eq_zero hij,
        b.orthonormal.norm_eq_one i, b.orthonormal.norm_eq_one j]
      norm_num
    have hdist : dist (b i) (b j) < 1 / 2 := by
      have ht := dist_triangle (b i) x (b j)
      have hx1 : dist (b i) x < 1 / 4 := by simpa only [mem_ball, dist_comm] using hxi
      have hx2 : dist x (b j) < 1 / 4 := hxj
      linarith
    nlinarith [show 0 ≤ dist (b i) (b j) from dist_nonneg]
  exact hd.countable_of_isOpen_disjoint (fun _ => isOpen_ball)
    (fun i => ⟨b i, by simp⟩)

end SHEStochastic
