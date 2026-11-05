module

public import SHE.VectorFiniteDifferences
public import SHE.GaussianAffineBlocks

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.VectorRootClips
open GaussianVectorFractions GaussianAssignmentBlocks GaussianRoughBlocks
open scoped BigOperators
variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {n m : ℕ}

def affineSum (mean : W) (L : Fin n → V →L[ℝ] W) (x : Fin n → V) : W :=
  mean + ∑ j, L j (x j)

theorem affineSum_update (mean : W) (L : Fin n → V →L[ℝ] W) (x : Fin n → V) (i : Fin n) :
    affineSum mean L x-affineSum mean L (Function.update x i 0) = L i (x i) := by
  classical
  dsimp [affineSum]
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Function.update_of_ne hji]
  · simp

/-- Coordinate suppression in the original vector old fractions is an
actual mixed translation difference in the original projected vectors. -/
theorem fractionDifferences_eq_mixed (is : List (Fin n)) (hnd : is.Nodup)
    (f : W → ℝ) (mean : W) (L : Fin n → V →L[ℝ] W) (x : Fin n → V) :
    fractionDifferences is (fun y => f (affineSum mean L y)) x =
      VectorFiniteDifferences.mixed (is.map (fun i => L i (x i))) f
        (affineSum mean L (suppress is x)) := by
  induction is generalizing x with
  | nil => rfl
  | cons i is ih =>
    obtain ⟨hi,hnd⟩ := List.nodup_cons.mp hnd
    change fractionDifferences is (fun y => f (affineSum mean L y)) x -
      fractionDifferences is (fun y => f (affineSum mean L y)) (Function.update x i 0) = _
    rw [ih hnd x, ih hnd (Function.update x i 0)]
    have hm : is.map (fun j => L j (Function.update x i 0 j)) =
        is.map (fun j => L j (x j)) := by
      apply List.map_congr_left
      intro j hj
      rw [Function.update_of_ne (by intro h; subst j; exact hi hj)]
    rw [hm, suppress_update is i hi x]
    have hx := affineSum_update mean L (suppress is x) i
    rw [suppress_apply_of_not_mem is i hi x] at hx
    have he : affineSum mean L (Function.update (suppress is x) i 0) + L i (x i) =
        affineSum mean L (suppress is x) := by rw [← hx]; abel
    simp only [List.map_cons,VectorFiniteDifferences.mixed,suppress]
    rw [suppress_update is i hi x,he]

/-- A genuine finite-dimensional cylinder has a clip for every assigned
old increment, with derivative bounds required only through that block's
finite order. The cylinder may depend jointly on all root coordinates. -/
theorem root_block_clipped_bound (choices : List (Fin n × Fin m))
    (hnd : (choices.map Prod.fst).Nodup) (factor : Fin m)
    (f : W → ℝ) {A ν : ℝ} (hA : 0 ≤ A) (hν : 0 ≤ ν)
    (hf : ContDiff ℝ (block choices factor).length f)
    (hb : ∀ j, j ≤ (block choices factor).length → ∀ z,
      ‖iteratedFDeriv ℝ j f z‖ ≤ A*ν^j)
    (mean : W) (L : Fin n → V →L[ℝ] W) (x : Fin n → V) :
    |fractionDifferences (block choices factor) (fun y => f (affineSum mean L y))
      (suppress (suppressed choices factor) x)| ≤
      (2 : ℝ)^(block choices factor).length*A*
        VectorFiniteDifferences.clips ν ((block choices factor).map (fun i => L i (x i))) := by
  rw [fractionDifferences_eq_mixed _ (block_nodup choices hnd factor)]
  have hm : (block choices factor).map (fun i => L i (suppress (suppressed choices factor) x i)) =
      (block choices factor).map (fun i => L i (x i)) := by
    apply List.map_congr_left
    intro i hi
    rw [suppress_assigned_coordinate choices hnd factor hi x]
  rw [hm]
  simpa only [Real.norm_eq_abs,List.length_map] using
    VectorFiniteDifferences.mixed_clipped_bound_finite (block choices factor).length W ℝ f
      ((block choices factor).map (fun i => L i (x i))) (by simp) hA hν hf hb
      (affineSum mean L (suppress (block choices factor) (suppress (suppressed choices factor) x)))

end SHE.VectorRootClips
