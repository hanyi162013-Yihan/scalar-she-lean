module

public import SHEStochastic.MatrixHaarNormalizedJets

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixHaarZerothBound
open Matrix MatrixFrobeniusNorm MatrixHaarJetBounds
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {d : Type*} [Fintype d] [DecidableEq d]

def constant (d : Type*) [Fintype d] (m U : ℝ) : ℝ :=
  inverseSize d m*inverseSize d (rootLower U)

theorem nonnegative (m U : ℝ) (hm : 0 < m) (hU : 0 < U) : 0 ≤ constant d m U := by
  unfold constant inverseSize rootLower
  positivity

/-- The zeroth-order child coefficients obey the same normalized
ellipticity-only control needed for the first physical derivative. -/
theorem children (A B : Matrix d d ℝ) (hA : A.PosDef) (hB : B.PosDef)
    (m U : ℝ) (hm : 0 < m) (hU : 0 < U)
    (hLo : m • (1 : Matrix d d ℝ) ≤ A ∧ m • (1 : Matrix d d ℝ) ≤ B)
    (hHi : A ≤ U • (1 : Matrix d d ℝ) ∧ B ≤ U • (1 : Matrix d d ℝ)) :
    size (MatrixHaarAlgebra.left A B) ≤ constant d m U ∧
      size (MatrixHaarAlgebra.right A B) ≤ constant d m U := by
  have hiA := MatrixEllipticSize.inverse A hA m hm hLo.1
  have hiB := MatrixEllipticSize.inverse B hB m hm hLo.2
  have hLowerA := (MatrixEllipticOrder.inverse_bounds A hA m U hm hLo.1 hHi.1).1
  have hLowerB := (MatrixEllipticOrder.inverse_bounds B hB m U hm hLo.2 hHi.2).1
  have hr : 0 < rootLower U := Real.sqrt_pos.mpr (div_pos (by norm_num) hU)
  have hLower : (rootLower U)^2 • (1 : Matrix d d ℝ) ≤ A⁻¹+B⁻¹ := by
    have he : U⁻¹+U⁻¹=(rootLower U)^2 := by
      rw [rootLower, Real.sq_sqrt (div_nonneg (by norm_num) hU.le)]
      ring
    simpa only [← add_smul, he] using add_le_add hLowerA hLowerB
  have hN := MatrixEllipticSize.inverse_sqrt (A⁻¹+B⁻¹) (hA.inv.add hB.inv) (rootLower U) hr hLower
  have hn : 0 ≤ inverseSize d m := div_nonneg (Real.sqrt_nonneg _) hm.le
  constructor
  · exact (MatrixFrobeniusNorm.mul _ _).trans (mul_le_mul hiA hN (MatrixFrobeniusNorm.nonneg _) hn)
  · change size (-(B⁻¹*MatrixHaarAlgebra.normalizer A B)) ≤ _
    rw [MatrixFrobeniusNorm.neg]
    exact (MatrixFrobeniusNorm.mul _ _).trans (mul_le_mul hiB hN (MatrixFrobeniusNorm.nonneg _) hn)

end SHEStochastic.MatrixHaarZerothBound
