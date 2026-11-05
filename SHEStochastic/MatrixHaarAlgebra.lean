module

public import Mathlib.Analysis.Matrix.Order

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic.MatrixHaarAlgebra
open Matrix
open scoped MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The ordered inverse square root used for a pair of child masses. -/
def normalizer (A B : Matrix n n ℝ) : Matrix n n ℝ :=
  (CFC.sqrt (A⁻¹ + B⁻¹))⁻¹

def left (A B : Matrix n n ℝ) : Matrix n n ℝ := A⁻¹ * normalizer A B

def right (A B : Matrix n n ℝ) : Matrix n n ℝ := -(B⁻¹ * normalizer A B)

theorem normalizer_hermitian (A B : Matrix n n ℝ) :
    (normalizer A B).IsHermitian := by
  apply Matrix.IsHermitian.inv
  exact (CFC.sqrt_nonneg (A⁻¹ + B⁻¹)).posSemidef.isHermitian

/-- Normalization preserves multiplication order; the child masses
are not assumed to commute. -/
theorem normalization (A B : Matrix n n ℝ) (hA : A.PosDef) (hB : B.PosDef) :
    normalizer A B * (A⁻¹ + B⁻¹) * normalizer A B = 1 := by
  let S := A⁻¹ + B⁻¹
  have hS : S.PosDef := hA.inv.add hB.inv
  have hs : 0 ≤ S := hS.posSemidef.nonneg
  have hroot : IsUnit (CFC.sqrt S) := (CFC.isUnit_sqrt_iff S hs).mpr hS.isUnit
  letI : Invertible (CFC.sqrt S) := hroot.invertible
  change (CFC.sqrt S)⁻¹ * S * (CFC.sqrt S)⁻¹ = 1
  calc
    _ = (CFC.sqrt S)⁻¹ * (CFC.sqrt S * CFC.sqrt S) * (CFC.sqrt S)⁻¹ :=
      congrArg (fun T ↦ (CFC.sqrt S)⁻¹ * T * (CFC.sqrt S)⁻¹)
        (CFC.sqrt_mul_sqrt_self S hs).symm
    _ = 1 := by
      simp only [← mul_assoc, Matrix.inv_mul_of_invertible, one_mul,
        Matrix.mul_inv_of_invertible]

/-- The weighted integral of a nonconstant block column vanishes. -/
theorem weighted_mean (A B : Matrix n n ℝ) (hA : A.PosDef) (hB : B.PosDef) :
    A * left A B + B * right A B = 0 := by
  letI : Invertible A := hA.isUnit.invertible
  letI : Invertible B := hB.isUnit.invertible
  simp only [left, right, mul_neg, ← mul_assoc, Matrix.mul_inv_of_invertible,
    one_mul, add_neg_cancel]

/-- The two children give exactly the identity matrix as weighted Gram
matrix, including all off-diagonal state components. -/
theorem weighted_gram (A B : Matrix n n ℝ) (hA : A.PosDef) (hB : B.PosDef) :
    (left A B)ᴴ * A * left A B + (right A B)ᴴ * B * right A B = 1 := by
  letI : Invertible A := hA.isUnit.invertible
  letI : Invertible B := hB.isUnit.invertible
  have hH := normalizer_hermitian A B
  have hAI := hA.inv.isHermitian
  have hBI := hB.inv.isHermitian
  simp only [left, right, conjTranspose_mul, conjTranspose_neg, hH.eq, hAI.eq, hBI.eq,
    neg_mul, mul_neg, neg_neg]
  calc
    _ = normalizer A B * (A⁻¹ + B⁻¹) * normalizer A B := by
      simp only [mul_add, add_mul, mul_assoc,
        ← mul_assoc A A⁻¹, ← mul_assoc B B⁻¹,
        Matrix.mul_inv_of_invertible, one_mul]
    _ = 1 := normalization A B hA hB

/-- Pairing with a block constant also vanishes. This is the local
orthogonality identity used for nested Haar intervals. -/
theorem constant_orthogonal (A B C : Matrix n n ℝ) (hA : A.PosDef) (hB : B.PosDef) :
    Cᴴ * A * left A B + Cᴴ * B * right A B = 0 := by
  rw [mul_assoc, mul_assoc, ← mul_add, weighted_mean A B hA hB, mul_zero]

end SHEStochastic.MatrixHaarAlgebra
