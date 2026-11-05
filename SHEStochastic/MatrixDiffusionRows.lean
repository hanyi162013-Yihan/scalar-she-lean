module

public import SHEStochastic.MatrixNonlinearCoefficient

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.MatrixDiffusionRows
open MeasureTheory
open scoped NNReal Matrix.Norms.L2Operator
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The i-th noise row as a vector: the adjoint diffusion applied to e_i. -/
def row (i : d) (A : Matrix d d ℝ) : EuclideanSpace ℝ d :=
  (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) A).adjoint (EuclideanSpace.single i 1)

theorem norm_le (i : d) (A : Matrix d d ℝ) : ‖row i A‖ ≤ ‖A‖ := by
  have hn : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := EuclideanSpace.orthonormal_single.norm_eq_one i
  have h := (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) A).adjoint.le_opNorm (EuclideanSpace.single i 1)
  rw [hn,mul_one,ContinuousLinearMap.adjoint.norm_map] at h
  exact h

theorem sub (i : d) (A B : Matrix d d ℝ) : row i A-row i B=row i (A-B) := by
  simp only [row,map_sub,_root_.sub_apply]

/-- Extracting a row preserves the operator-norm modulus of continuity. -/
theorem lipschitz (i : d) : LipschitzWith 1 (row i) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  simpa only [NNReal.coe_one,one_mul,dist_eq_norm,sub] using norm_le i (A-B)

theorem holder {X : Type*} [PseudoEMetricSpace X] {G : X → Matrix d d ℝ} {C β : ℝ≥0}
    (hG : HolderWith C β G) (i : d) : HolderWith C β (fun z => row i (G z)) := by
  simpa only [NNReal.coe_one,NNReal.rpow_one,one_mul,Function.comp_def]
    using (lipschitz i).holderWith.comp hG

theorem coefficient_bound (G : MatrixNonlinearCoefficient.Coefficient d) (i : d)
    (z : EuclideanSpace ℝ d) : ‖row i (G.value z)‖ ≤ G.bound :=
  (norm_le i (G.value z)).trans (G.norm_bound z)

end SHEStochastic.MatrixDiffusionRows
