module

public import SHE.GaussianRoughBlocks
public import SHE.FiniteDifferences

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.GaussianAffineBlocks
open GaussianVectorFractions GaussianAssignmentBlocks GaussianRoughBlocks
open scoped BigOperators
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n m : ℕ}

/-- A vector-coordinate old block is literally the scalar mixed finite
difference in the original projected increments. Its base point contains
exactly the unassigned increments. -/
theorem fractionDifferences_eq_mixed (is : List (Fin n)) (hnd : is.Nodup)
    (a : ℝ → ℝ) (mean : ℝ) (L : Fin n → V →L[ℝ] ℝ) (x : Fin n → V) :
    fractionDifferences is (fun y => a (affineSum mean L y)) x =
      FiniteDifferences.mixed (is.map (fun i => L i (x i))) a
        (affineSum mean L (suppress is x)) := by
  induction is generalizing x with
  | nil => rfl
  | cons i is ih =>
    obtain ⟨hi, hnd⟩ := List.nodup_cons.mp hnd
    change fractionDifferences is (fun y => a (affineSum mean L y)) x -
      fractionDifferences is (fun y => a (affineSum mean L y)) (Function.update x i 0) = _
    rw [ih hnd x, ih hnd (Function.update x i 0)]
    have hm : is.map (fun j => L j (Function.update x i 0 j)) =
        is.map (fun j => L j (x j)) := by
      apply List.map_congr_left
      intro j hj
      rw [Function.update_of_ne (by intro h; subst j; exact hi hj)]
    rw [hm, suppress_update is i hi x]
    have hx := affineSum_update mean L (suppress is x) i
    rw [suppress_apply_of_not_mem is i hi x] at hx
    simp only [List.map_cons, FiniteDifferences.mixed, FiniteDifferences.difference, suppress]
    rw [suppress_update is i hi x]
    have he : affineSum mean L (Function.update (suppress is x) i 0) + L i (x i) =
        affineSum mean L (suppress is x) := by linarith
    rw [he]

/-- Canonical assignment suppression leaves every assigned increment
unchanged, so the actual clipped root uses the original increment laws. -/
theorem suppressed_block_eq_mixed (choices : List (Fin n × Fin m))
    (hnd : (choices.map Prod.fst).Nodup) (k : Fin m)
    (a : ℝ → ℝ) (mean : ℝ) (L : Fin n → V →L[ℝ] ℝ) (x : Fin n → V) :
    fractionDifferences (block choices k) (fun y => a (affineSum mean L y))
      (suppress (suppressed choices k) x) =
      FiniteDifferences.mixed ((block choices k).map (fun i => L i (x i))) a
        (affineSum mean L (suppress (block choices k) (suppress (suppressed choices k) x))) := by
  rw [fractionDifferences_eq_mixed _ (block_nodup choices hnd k)]
  have hm : (block choices k).map (fun i => L i (suppress (suppressed choices k) x i)) =
      (block choices k).map (fun i => L i (x i)) := by
    apply List.map_congr_left
    intro i hi
    rw [suppress_assigned_coordinate choices hnd k hi x]
  rw [hm]

end SHE.GaussianAffineBlocks
