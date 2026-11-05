module

public import SHEStochastic.MatrixFrobeniusNorm
public import SHEStochastic.MatrixSqrtDerivative

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixEllipticSize
open Matrix SHE.FiniteTransport MatrixFrobeniusNorm
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem quadratic (A : Matrix d d ℝ) (m : ℝ)
    (hLo : m • (1 : Matrix d d ℝ) ≤ A) (v : d → ℝ) :
    m*vectorSq v ≤ v ⬝ᵥ (A*ᵥv) := by
  have hp : (A-m • (1 : Matrix d d ℝ)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hLo)
  have hh := hp.dotProduct_mulVec_nonneg v
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_smul] at hh
  have he : v ⬝ᵥ v = vectorSq v := by simp only [dotProduct, vectorSq, pow_two]
  rw [he, smul_eq_mul] at hh
  linarith

/-- A literal inverse-matrix Frobenius bound from ellipticity, valid
also for noncommuting matrix families. -/
theorem inverse (A : Matrix d d ℝ) (hp : A.PosDef) (m : ℝ) (hm : 0<m)
    (hLo : m • (1 : Matrix d d ℝ) ≤ A) :
    size A⁻¹ ≤ Real.sqrt (Fintype.card d : ℝ)/m := by
  letI : Invertible A := hp.isUnit.invertible
  have hh := MatrixSylvesterFrobenius.lower A (0 : Matrix d d ℝ) A⁻¹ m 0 (by linarith)
    (quadratic A m hLo) (by intro v; simp [dotProduct])
  simp only [add_zero, Matrix.mul_inv_of_invertible, mul_zero] at hh
  have hone : frobeniusSq (1 : Matrix d d ℝ) = (Fintype.card d : ℝ) := by
    simp [frobeniusSq, Matrix.one_apply]
  rw [hone] at hh
  have hs : (m*size A⁻¹)^2 ≤ (Real.sqrt (Fintype.card d : ℝ))^2 := by
    rw [mul_pow, square, Real.sq_sqrt (by positivity)]
    exact hh
  have hbound := (sq_le_sq₀ (mul_nonneg hm.le (nonneg _)) (Real.sqrt_nonneg _)).mp hs
  exact (le_div_iff₀ hm).mpr (by nlinarith only [hbound])

theorem inverse_sqrt (A : Matrix d d ℝ) (hp : A.PosDef) (r : ℝ) (hr : 0<r)
    (hLo : r^2 • (1 : Matrix d d ℝ) ≤ A) :
    size (CFC.sqrt A)⁻¹ ≤ Real.sqrt (Fintype.card d : ℝ)/r :=
  inverse (CFC.sqrt A) (MatrixHaarPositive.sqrt_posDef A hp) r hr
    (MatrixSqrtDerivative.lower A r hr.le hLo)

end SHEStochastic.MatrixEllipticSize
