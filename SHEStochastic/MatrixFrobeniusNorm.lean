module

public import SHE.SignedTransport
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.MatrixFrobeniusNorm
open Matrix SHE.FiniteTransport

variable {d k m : Type*} [Fintype d] [Fintype k] [Fintype m]

/-- Frobenius size as an explicit scalar, independent of whichever
matrix operator norm is active in differentiation theorems. -/
def size (A : Matrix d k ℝ) : ℝ := Real.sqrt (frobeniusSq A)

theorem nonneg (A : Matrix d k ℝ) : 0 ≤ size A := Real.sqrt_nonneg _

theorem square (A : Matrix d k ℝ) : size A^2 = frobeniusSq A :=
  Real.sq_sqrt (frobeniusSq_nonneg A)

section
open scoped Matrix.Norms.Frobenius

private theorem size_eq_norm (A : Matrix d k ℝ) : size A=‖A‖ := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  unfold size
  congr 1
  simp only [frobeniusSq, Real.rpow_two, Real.norm_eq_abs, sq_abs]

theorem add (A B : Matrix d k ℝ) : size (A+B) ≤ size A+size B := by
  simpa only [size_eq_norm] using norm_add_le A B

theorem sub (A B : Matrix d k ℝ) : size (A-B) ≤ size A+size B := by
  simpa only [size_eq_norm] using norm_sub_le A B

theorem neg (A : Matrix d k ℝ) : size (-A)=size A := by simp only [size_eq_norm, norm_neg]

theorem mul (A : Matrix d k ℝ) (B : Matrix k m ℝ) : size (A*B) ≤ size A*size B := by
  simpa only [size_eq_norm] using Matrix.frobenius_norm_mul A B

end

theorem zero : size (0 : Matrix d k ℝ)=0 := by simp [size, frobeniusSq]

theorem list_sum (l : List (Matrix d k ℝ)) : size l.sum ≤ (l.map size).sum := by
  induction l with
  | nil => simp only [List.sum_nil, List.map_nil, zero, le_refl]
  | cons A l ih =>
    simp only [List.sum_cons, List.map_cons]
    exact (add A l.sum).trans (add_le_add le_rfl ih)

theorem sum_map_le {X : Type*} (l : List X) (f g : X → ℝ)
    (h : ∀ x∈l, f x≤g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => exact le_rfl
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h x (List.mem_cons_self))
      (ih (fun y hy ↦ h y (List.mem_cons_of_mem _ hy)))

/-- Finite sums of ordered matrix products are controlled by the
corresponding scalar sum of Frobenius products. -/
theorem list_products {X : Type*} (l : List X) (A : X → Matrix d k ℝ) (B : X → Matrix k m ℝ) :
    size ((l.map (fun x ↦ A x*B x)).sum) ≤ (l.map (fun x ↦ size (A x)*size (B x))).sum := by
  apply (list_sum (l.map (fun x ↦ A x*B x))).trans
  simp only [List.map_map, Function.comp_def]
  exact sum_map_le l _ _ (fun x _ ↦ mul (A x) (B x))

end SHEStochastic.MatrixFrobeniusNorm
