module

public import SHEStochastic.MatrixEllipticOrder

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.MatrixSelfAdjointNormBounds
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem bound (A : Matrix d d ℝ) (hA : A.IsHermitian) :
    -‖A‖ • (1 : Matrix d d ℝ) ≤ A ∧ A ≤ ‖A‖ • (1 : Matrix d d ℝ) := by
  cases isEmpty_or_nonempty d with
  | inl h =>
    letI := h
    have he : A = 0 := Subsingleton.elim _ _
    simp [he]
  | inr h =>
    letI := h
    have hsa : IsSelfAdjoint A := hA
    constructor
    · rw [← Algebra.algebraMap_eq_smul_one]
      apply (algebraMap_le_iff_le_spectrum hsa).mpr
      intro t ht
      have hh := spectrum.norm_le_norm_of_mem ht
      exact (neg_le_neg (show |t| ≤ ‖A‖ from hh)).trans (neg_abs_le t)
    · rw [← Algebra.algebraMap_eq_smul_one]
      apply (le_algebraMap_iff_spectrum_le hsa).mpr
      intro t ht
      exact (le_abs_self t).trans (spectrum.norm_le_norm_of_mem ht)

end SHEStochastic.MatrixSelfAdjointNormBounds
