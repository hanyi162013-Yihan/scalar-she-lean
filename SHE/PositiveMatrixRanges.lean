module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real

@[expose] public section
set_option autoImplicit false
noncomputable section

/-! Range inclusion follows from positive semidefinite domination, including
singular matrices. No strict positivity or inverse is required. -/
namespace SHE.PositiveMatrixRanges

open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A B : Matrix ι ι ℝ}

theorem kernel_le_of_domination (hB : B.PosSemidef) (C : ℝ)
    (hAB : (C • A - B).PosSemidef) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) A).ker ≤
      (Matrix.toEuclideanCLM (𝕜 := ℝ) B).ker := by
  intro x hx
  change Matrix.toEuclideanCLM (𝕜 := ℝ) A x = 0 at hx
  change Matrix.toEuclideanCLM (𝕜 := ℝ) B x = 0
  have hAx : A *ᵥ WithLp.ofLp x = 0 := by
    simpa using congrArg (WithLp.ofLp (p := 2)) hx
  have hqB := hB.dotProduct_mulVec_nonneg (WithLp.ofLp x)
  have hqAB := hAB.dotProduct_mulVec_nonneg (WithLp.ofLp x)
  have hz : star (WithLp.ofLp x) ⬝ᵥ B *ᵥ WithLp.ofLp x = 0 := by
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, hAx, smul_zero,
      zero_sub, dotProduct_neg] at hqAB
    exact le_antisymm (neg_nonneg.mp hqAB) hqB
  have hBx := hB.dotProduct_mulVec_zero_iff.mp hz
  apply WithLp.ofLp_injective
  simpa using hBx

theorem range_le_of_domination (hA : A.PosSemidef) (hB : B.PosSemidef) (C : ℝ)
    (hAB : (C • A - B).PosSemidef) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) B).range ≤
      (Matrix.toEuclideanCLM (𝕜 := ℝ) A).range := by
  have hSA : A.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hA.isHermitian
  have hSB : B.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hB.isHermitian
  apply Submodule.orthogonal_le_orthogonal_iff.mp
  change (LinearMap.range A.toEuclideanLin)ᗮ ≤ (LinearMap.range B.toEuclideanLin)ᗮ
  rw [hSA.orthogonal_range, hSB.orthogonal_range]
  exact kernel_le_of_domination hB C hAB

theorem range_le_add_right (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) A).range ≤
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (A + B)).range := by
  apply range_le_of_domination (hA.add hB) hA 1
  simpa only [one_smul, add_sub_cancel_left] using hB

theorem range_le_add_left (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) B).range ≤
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (A + B)).range := by
  simpa only [add_comm] using range_le_add_right hB hA

end SHE.PositiveMatrixRanges
