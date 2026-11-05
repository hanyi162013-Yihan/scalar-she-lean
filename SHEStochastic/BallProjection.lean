module

public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.BallProjection
open Set Metric
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The metric projection onto a closed Hilbert ball. Its construction
reuses mathlib's Hilbert projection theorem. -/
def project (R : ℝ≥0) (x : E) : E := Classical.choose
  (exists_norm_eq_iInf_of_complete_convex
    (show (closedBall (0 : E) R).Nonempty from ⟨0, by simp⟩)
    isClosed_closedBall.isComplete (convex_closedBall (0 : E) R) x)

theorem mem_ball (R : ℝ≥0) (x : E) : project R x ∈ closedBall (0 : E) R :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex
    (show (closedBall (0 : E) R).Nonempty from ⟨0, by simp⟩)
    isClosed_closedBall.isComplete (convex_closedBall (0 : E) R) x)).1

theorem variational (R : ℝ≥0) (x y : E) (hy : y ∈ closedBall (0 : E) R) :
    inner ℝ (x - project R x) (y - project R x) ≤ 0 := by
  apply (norm_eq_iInf_iff_real_inner_le_zero (convex_closedBall (0 : E) R) (mem_ball R x)).mp _ y hy
  exact (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex
    (show (closedBall (0 : E) R).Nonempty from ⟨0, by simp⟩)
    isClosed_closedBall.isComplete (convex_closedBall (0 : E) R) x)).2

theorem of_norm_le (R : ℝ≥0) {x : E} (hx : ‖x‖ ≤ R) : project R x = x := by
  have hh := variational R x x (by simpa only [mem_closedBall, dist_zero_right] using hx)
  rw [real_inner_self_eq_norm_sq] at hh
  have hz : ‖x - project R x‖ = 0 := by nlinarith [norm_nonneg (x - project R x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

theorem norm_le_radius (R : ℝ≥0) (x : E) : ‖project R x‖ ≤ R := by
  simpa only [mem_closedBall, dist_zero_right] using mem_ball R x

theorem norm_le (R : ℝ≥0) (x : E) : ‖project R x‖ ≤ ‖x‖ := by
  by_cases hx : ‖x‖ ≤ R
  · rw [of_norm_le R hx]
  · exact (norm_le_radius R x).trans (le_of_not_ge hx)

/-- Nonexpansiveness is proved from the two variational inequalities;
the constant is exactly one, independent of the radius or dimension. -/
theorem norm_sub_le (R : ℝ≥0) (x y : E) : ‖project R x - project R y‖ ≤ ‖x - y‖ := by
  let u := project R x
  let v := project R y
  have h1 : 0 ≤ inner ℝ (x - u) (u - v) := by
    have hh := variational R x v (mem_ball R y)
    rw [show v - project R x = -(u - v) by dsimp [u]; abel, inner_neg_right] at hh
    linarith
  have h2 : inner ℝ (y - v) (u - v) ≤ 0 := variational R y u (mem_ball R x)
  have he : inner ℝ (x - y) (u - v) =
      inner ℝ (x - u) (u - v) + ‖u - v‖ ^ 2 - inner ℝ (y - v) (u - v) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    ring
  have hh := real_inner_le_norm (x - y) (u - v)
  have hn := norm_nonneg (u - v)
  change ‖u - v‖ ≤ ‖x - y‖
  by_cases hz : ‖u - v‖ = 0
  · simpa only [hz] using norm_nonneg (x - y)
  · have hp : 0 < ‖u - v‖ := lt_of_le_of_ne hn (Ne.symm hz)
    nlinarith

theorem lipschitz (R : ℝ≥0) : LipschitzWith 1 (project (E := E) R) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using norm_sub_le R x y

end SHEStochastic.BallProjection
