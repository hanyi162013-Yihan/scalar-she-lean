module

public import SHEStochastic.MatrixSqrtReference

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixEllipticOperatorNorm
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The real matrix operator norm is controlled by its positive order
bound, proved through the actual square root and quadratic estimates. -/
theorem upper (A : Matrix d d ℝ) (hA : 0 ≤ A) (U : ℝ) (hU : 0 ≤ U)
    (hHi : A ≤ U • (1 : Matrix d d ℝ)) : ‖A‖ ≤ U := by
  let S := Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (CFC.sqrt A)
  have hsq : S.adjoint.comp S=Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) A := by
    change star (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (CFC.sqrt A))*
      Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (CFC.sqrt A)=_
    rw [← map_star, ← map_mul, (CFC.sqrt_nonneg A).star_eq, CFC.sqrt_mul_sqrt_self A hA]
  have hS : ‖S‖ ≤ Real.sqrt U := by
    apply S.opNorm_le_bound (Real.sqrt_nonneg U)
    intro v
    have hh := ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right S v
    rw [hsq] at hh
    have hb := MatrixFieldQuadratic.upper A U hHi v
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg U) (norm_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt hU, hh]
    exact hb
  have hNorm : ‖CFC.sqrt A‖ ≤ Real.sqrt U := hS
  rw [← MatrixSqrtReference.sqrt_norm_sq A hA]
  exact (pow_le_pow_left₀ (norm_nonneg _) hNorm 2).trans_eq (Real.sq_sqrt hU)

end SHEStochastic.MatrixEllipticOperatorNorm
