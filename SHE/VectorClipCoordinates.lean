module

public import SHE.VectorRootClips
public import SHE.GaussianClipProducts

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.VectorClipCoordinates
open GaussianIncrement GaussianClipMoments
open scoped BigOperators

theorem norm_le_sum_abs {n : ℕ} (z : State n) : ‖z‖ ≤ ∑ i, |z i| := by
  have he : (∑ i : Fin n, z i • EuclideanSpace.basisFun (Fin n) ℝ i) = z := by
    simpa only [EuclideanSpace.basisFun_repr] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr z
  calc
    ‖z‖ = ‖∑ i : Fin n, z i • EuclideanSpace.basisFun (Fin n) ℝ i‖ := by rw [he]
    _ ≤ ∑ i : Fin n, ‖z i • EuclideanSpace.basisFun (Fin n) ℝ i‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_smul,Real.norm_eq_abs,
      (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one,mul_one]

theorem min_one_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min 1 (a+b) ≤ min 1 a+min 1 b := by
  by_cases h1 : a ≤ 1
  · rw [min_eq_right h1]
    by_cases h2 : b ≤ 1
    · rw [min_eq_right h2]; exact min_le_right _ _
    · rw [min_eq_left (le_of_not_ge h2)]
      exact (min_le_left _ _).trans (by linarith)
  · rw [min_eq_left (le_of_not_ge h1)]
    exact (min_le_left _ _).trans (by linarith [le_min (by norm_num : (0:ℝ) ≤ 1) hb])

theorem min_one_sum_le {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    min 1 (∑ i ∈ s,a i) ≤ ∑ i ∈ s,min 1 (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact (min_one_add_le (ha i (Finset.mem_insert_self _ _))
      (Finset.sum_nonneg (fun j hj => ha j (Finset.mem_insert_of_mem hj)))).trans
      (add_le_add le_rfl (ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))))

/-- A vector root clip is bounded by the sum of the original coordinate
clips. This uses the finite root dimension, with no scalar-root assumption. -/
theorem vector_clip_le_sum {n : ℕ} {ν : ℝ} (hν : 0 ≤ ν) (z : State n) :
    min 1 (ν*‖z‖) ≤ ∑ i : Fin n,clip ν (z i) := by
  calc
    _ ≤ min 1 (ν*∑ i,|z i|) := min_le_min_left _ (mul_le_mul_of_nonneg_left (norm_le_sum_abs z) hν)
    _ = min 1 (∑ i,ν*|z i|) := by rw [Finset.mul_sum]
    _ ≤ _ := min_one_sum_le Finset.univ _ (fun i _ => mul_nonneg hν (abs_nonneg _))

/-- Every assigned vector root increment keeps its original Gaussian
coordinate. The finite coordinate assignments may be integrated jointly
with arbitrarily dependent scores and rough factors. -/
theorem vector_clips_le_coordinate_assignments {n r : ℕ} {ν : ℝ}
    (hν : 0 ≤ ν) (z : Fin r → State n) :
    (∏ j,min 1 (ν*‖z j‖)) ≤
      ∑ choice : Fin r → Fin n,∏ j,clip ν (z j (choice j)) := by
  calc
    _ ≤ ∏ j,∑ i : Fin n,clip ν (z j i) :=
      Finset.prod_le_prod₀ (fun j _ => le_min (by norm_num) (mul_nonneg hν (norm_nonneg _)))
        (fun j _ => vector_clip_le_sum hν (z j))
    _ = _ := Fintype.prod_sum _

end SHE.VectorClipCoordinates
