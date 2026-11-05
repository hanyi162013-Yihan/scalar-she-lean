module

public import SHE.CovarianceMatrix

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.PositiveMatrixBounds
open Matrix Finset SHE.WordRecursion

theorem diag_le_trace {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (i : Fin n) :
    A i i ≤ A.trace := by
  unfold Matrix.trace
  exact single_le_sum (f:=fun j : Fin n => A j j) (fun j _ => hA.diag_nonneg) (mem_univ i)

theorem abs_entry_le_trace {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (i j : Fin n) : |A i j| ≤ A.trace := by
  have hp := hA.dotProduct_mulVec_nonneg (Pi.single i 1+Pi.single j 1)
  have hm := hA.dotProduct_mulVec_nonneg (Pi.single i 1-Pi.single j 1)
  simp only [star_trivial,mulVec_add,mulVec_sub,add_dotProduct,sub_dotProduct,
    dotProduct_add,dotProduct_sub,mulVec_single_one,single_dotProduct,one_mul,
    Matrix.col_apply] at hp hm
  have hsym : A j i=A i j := by simpa only [star_trivial] using hA.isHermitian.apply i j
  rw [hsym] at hp hm
  exact abs_le.mpr ⟨by linarith [diag_le_trace hA i,diag_le_trace hA j],
    by linarith [diag_le_trace hA i,diag_le_trace hA j]⟩

theorem bilinear_basis_bound {n : ℕ} (H : State n →L[ℝ] State n →L[ℝ] ℝ) (i j : Fin n) :
    ‖H (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)‖ ≤ ‖H‖ := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hn (k : Fin n) : ‖e k‖=1 := e.orthonormal.norm_eq_one k
  calc
    _ ≤ ‖H (e i)‖*‖e j‖ := (H (e i)).le_opNorm (e j)
    _ ≤ (‖H‖*‖e i‖)*‖e j‖ := mul_le_mul_of_nonneg_right (H.le_opNorm (e i)) (norm_nonneg _)
    _ = _ := by rw [hn,hn,mul_one,mul_one]

/-- The actual mixed covariance/Hessian action is bounded by trace,
including every off-diagonal entry and singular PSD matrices. -/
theorem covariance_action_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (H : State n →L[ℝ] State n →L[ℝ] ℝ) :
    ‖∑ i : Fin n,∑ j : Fin n,A i j*
      H (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)‖ ≤
        (n:ℝ)^2*A.trace*‖H‖ := by
  calc
    _ ≤ ∑ i : Fin n,∑ j : Fin n,‖A i j*
        H (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)‖ :=
      (norm_sum_le _ _).trans (sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ _i : Fin n,∑ _j : Fin n,A.trace*‖H‖ := sum_le_sum (fun i _ => sum_le_sum (fun j _ => by
      rw [norm_mul,Real.norm_eq_abs]
      exact mul_le_mul (abs_entry_le_trace hA i j) (bilinear_basis_bound H i j)
        (norm_nonneg _) hA.trace_nonneg))
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul];ring

end SHE.PositiveMatrixBounds
