module

public import SHEStochastic.MatrixFiniteFactor

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.MatrixHaarPositive
open Matrix MatrixHaarAlgebra MatrixFiniteHaar
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem sqrt_posDef (A : Matrix d d ℝ) (hA : A.PosDef) : (CFC.sqrt A).PosDef := by
  have hn : 0≤A := hA.posSemidef.nonneg
  have hu : IsUnit (CFC.sqrt A) := (CFC.isUnit_sqrt_iff A hn).mpr hA.isUnit
  exact ((CFC.sqrt_nonneg A).posSemidef.posDef_iff_isUnit).mpr hu

theorem normalizer_posDef (A B : Matrix d d ℝ) (hA : A.PosDef) (hB : B.PosDef) :
    (normalizer A B).PosDef := (sqrt_posDef _ (hA.inv.add hB.inv)).inv

theorem mass_left (A B : Matrix d d ℝ) (hA : A.PosDef) : A*left A B=normalizer A B := by
  letI : Invertible A := hA.isUnit.invertible
  simp only [left, ← mul_assoc, Matrix.mul_inv_of_invertible, one_mul]

theorem mass_right (A B : Matrix d d ℝ) (hB : B.PosDef) : B*right A B= -normalizer A B := by
  letI : Invertible B := hB.isUnit.invertible
  simp only [right, mul_neg, ← mul_assoc, Matrix.mul_inv_of_invertible, one_mul]

/-- At the root the finite factor's diagonal is a positive square root. -/
theorem mass_inverseSqrt (A : Matrix d d ℝ) (hA : A.PosDef) : A*inverseSqrt A=CFC.sqrt A := by
  have hn : 0≤A := hA.posSemidef.nonneg
  have hu : IsUnit (CFC.sqrt A) := (CFC.isUnit_sqrt_iff A hn).mpr hA.isUnit
  letI : Invertible (CFC.sqrt A) := hu.invertible
  change A*(CFC.sqrt A)⁻¹=CFC.sqrt A
  calc
    _ = (CFC.sqrt A*CFC.sqrt A)*(CFC.sqrt A)⁻¹ :=
      congrArg (fun B ↦ B*(CFC.sqrt A)⁻¹) (CFC.sqrt_mul_sqrt_self A hn).symm
    _ = _ := by rw [mul_assoc, Matrix.mul_inv_of_invertible, mul_one]

end SHEStochastic.MatrixHaarPositive
