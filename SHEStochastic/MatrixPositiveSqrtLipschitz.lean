module

public import SHEStochastic.MatrixSqrtDerivative
public import SHEStochastic.MatrixProfileHilbert

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixPositiveSqrtLipschitz
open Matrix MatrixFrobeniusNorm SHE.FiniteTransport
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Signed square-root stability follows directly from the existing
noncommuting Sylvester comparison, without a new interpolation proof. -/
theorem size_bound (A B : Matrix d d ℝ) {r : ℝ} (hr : 0 < r)
    (hA : r^2 • (1 : Matrix d d ℝ) ≤ A) (hB : r^2 • (1 : Matrix d d ℝ) ≤ B) :
    size (CFC.sqrt A-CFC.sqrt B) ≤ size (A-B)/(2*r) := by
  have hA0 : 0 ≤ A := (smul_nonneg (sq_nonneg r) zero_le_one).trans hA
  have hB0 : 0 ≤ B := (smul_nonneg (sq_nonneg r) zero_le_one).trans hB
  have hsym : (CFC.sqrt B)ᵀ=CFC.sqrt B := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg B).posSemidef.isHermitian.eq
  have hs := MatrixSylvesterFrobenius.difference_sq (CFC.sqrt A) (CFC.sqrt B) r r
    (by linarith) (MatrixSqrtDerivative.quadratic_lower A r hr.le hA)
    (by rw [hsym]; exact MatrixSqrtDerivative.quadratic_lower B r hr.le hB)
  rw [CFC.sqrt_mul_sqrt_self A hA0,CFC.sqrt_mul_sqrt_self B hB0] at hs
  have hsq : (2*r*size (CFC.sqrt A-CFC.sqrt B))^2 ≤ size (A-B)^2 := by
    rw [mul_pow,square,square]
    convert hs using 1 <;> ring
  have hn := (sq_le_sq₀ (mul_nonneg (by positivity) (nonneg _)) (nonneg (A-B))).mp hsq
  apply (le_div_iff₀ (by positivity : 0 < 2*r)).mpr
  simpa only [mul_comm] using hn

def constant (d : Type*) [Fintype d] [DecidableEq d] (r : ℝ) : ℝ :=
  ‖MatrixProfileHilbert.toMatrix d‖/(2*r)*‖MatrixProfileHilbert.toVector d‖

theorem constant_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ constant d r :=
  mul_nonneg (div_nonneg (norm_nonneg (MatrixProfileHilbert.toMatrix d)) (by positivity))
    (norm_nonneg (MatrixProfileHilbert.toVector d))

theorem bound (A B : Matrix d d ℝ) {r : ℝ} (hr : 0 < r)
    (hA : r^2 • (1 : Matrix d d ℝ) ≤ A) (hB : r^2 • (1 : Matrix d d ℝ) ≤ B) :
    ‖CFC.sqrt A-CFC.sqrt B‖ ≤ constant d r*‖A-B‖ := by
  have he (C : Matrix d d ℝ) : ‖C‖ ≤ ‖MatrixProfileHilbert.toMatrix d‖*size C := by
    have hh := (MatrixProfileHilbert.toMatrix d).le_opNorm (MatrixProfileHilbert.toVector d C)
    rw [MatrixProfileHilbert.norm_vector] at hh
    exact hh
  have hi : size (A-B) ≤ ‖MatrixProfileHilbert.toVector d‖*‖A-B‖ := by
    rw [← MatrixProfileHilbert.norm_vector]
    exact (MatrixProfileHilbert.toVector d).le_opNorm _
  calc
    _ ≤ _ := he _
    _ ≤ ‖MatrixProfileHilbert.toMatrix d‖*(size (A-B)/(2*r)) :=
      mul_le_mul_of_nonneg_left (size_bound A B hr hA hB) (norm_nonneg (MatrixProfileHilbert.toMatrix d))
    _ ≤ ‖MatrixProfileHilbert.toMatrix d‖*((‖MatrixProfileHilbert.toVector d‖*‖A-B‖)/(2*r)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hi (by positivity))
        (norm_nonneg (MatrixProfileHilbert.toMatrix d))
    _ = _ := by unfold constant; ring

end SHEStochastic.MatrixPositiveSqrtLipschitz
