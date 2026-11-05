module

public import SHEStochastic.MatrixDirectionBounds
public import SHEStochastic.DyadicCellRefinement
public import SHE.HaarHigherColumns

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixDirectionEnergy
open MeasureTheory SHE SHE.FiniteHaar MatrixPhysicalColumnSmooth MatrixProfileHilbert
open MatrixDirectionBounds MatrixActualColumnCalculus
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem sum_cell_energy (n : ℕ) (v : Domain (d := d)) :
    (∑ x : Grid n, ‖restricted (cellSet n x) (measurableSet_cellSet n x) v‖ ^ 2) = ‖v‖ ^ 2 := by
  have hi : Integrable (fun x => ‖v.val x‖ ^ 2) μ := by
    simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) v.val v.val
  have hh := DyadicCellRefinement.integral_partition n (fun x => ‖v.val x‖ ^ 2) hi
  simp_rw [show ∀ x : Grid n,
      ‖restricted (cellSet n x) (measurableSet_cellSet n x) v‖ ^ 2 =
        ∫ y in cellSet n x, ‖v.val y‖ ^ 2 ∂μ from
      fun x => MatrixProfileCellBounds.restriction_energy _ _ _]
  rw [← hh]
  have hn := L2.inner_def (𝕜 := ℝ) v.val v.val
  simp only [real_inner_self_eq_norm_sq] at hn
  convert! hn.symm using 1

/-- Localizing one arbitrary matrix direction on the two children of
every node counts each physical cell only once. -/
theorem generation (n : ℕ) (v : Domain (d := d)) :
    (∑ x : Grid n, localSize (leafPath n x) v ^ 2) ≤ 2 * ‖v‖ ^ 2 := by
  let a := fun k (x : Grid k) => ‖restricted (cellSet k x) (measurableSet_cellSet k x) v‖ ^ 2
  have hb (x : Grid n) (b : Bool) :
      ‖restricted (MatrixGlobalHaar.child (leafPath n x) b)
        (MatrixGlobalHaar.child_measurable (leafPath n x) b) v‖ ^ 2 = a (n+1) (leafChild n x b) := by
    exact leafPath_child_eval (fun k z => a k z) n x b
  calc
    _ ≤ ∑ x : Grid n, 2 * (a (n+1) (leafChild n x false) + a (n+1) (leafChild n x true)) := by
      apply Finset.sum_le_sum
      intro x hx
      unfold localSize
      rw [← hb x false, ← hb x true]
      nlinarith [sq_nonneg (‖restricted (MatrixGlobalHaar.child (leafPath n x) false)
        (MatrixGlobalHaar.child_measurable (leafPath n x) false) v‖ -
        ‖restricted (MatrixGlobalHaar.child (leafPath n x) true)
        (MatrixGlobalHaar.child_measurable (leafPath n x) true) v‖)]
    _ = 2 * ∑ x : Grid (n+1), a (n+1) x := by
      rw [sum_leafChildren n, Finset.mul_sum]
    _ = _ := by rw [show (∑ x : Grid (n+1), a (n+1) x) = ‖v‖ ^ 2 from sum_cell_energy (n+1) v]

end SHEStochastic.MatrixDirectionEnergy
