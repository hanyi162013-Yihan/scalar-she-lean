module

public import SHE.GaussianProfileMark

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.GaussianProfileMark
open Set MeasureTheory GaussianIncrement
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

def matrixApply (z : State n) : Mat n →L[ℝ] State n :=
  { toLinearMap :=
      { toFun := fun A => Matrix.toEuclideanCLM (𝕜 := ℝ) A z
        map_add' := by intro A B; simp
        map_smul' := by intro r A; simp }
    cont := by
      have hp : Continuous (fun A : Mat n => (A, z)) := continuous_id.prodMk continuous_const
      have hh := (Matrix.continuous_uncurry_toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).comp hp
      exact hh }

@[simp] theorem matrixApply_apply (z : State n) (A : Mat n) :
    matrixApply z A = Matrix.toEuclideanCLM (𝕜 := ℝ) A z := rfl

theorem rankMatrix_apply (v z : State n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (rankMatrix v) z = (inner ℝ v z) • v := by
  change (Matrix.toEuclideanLin (rankMatrix v)).toContinuousLinearMap z = _
  rw [rankMatrix, LinearEquiv.apply_symm_apply]
  rfl

/-- Literal action of the continuum covariance integral. -/
theorem profileCovariance_apply {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (c : X → ℝ) (v : X → State n)
    (hi : Integrable (fun x => c x • rankMatrix (v x)) μ) (z : State n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (profileCovariance μ c v) z =
      ∫ x, (c x * inner ℝ (v x) z) • v x ∂μ := by
  have hh := (matrixApply z).integral_comp_comm hi
  change (∫ x, matrixApply z (c x • rankMatrix (v x)) ∂μ) = _ at hh
  rw [show profileCovariance μ c v = ∫ x, c x • rankMatrix (v x) ∂μ from rfl]
  rw [← matrixApply_apply, ← hh]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  simp only [map_smul, matrixApply_apply, rankMatrix_apply, smul_smul]

theorem profileCovariance_quadratic {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (c : X → ℝ) (v : X → State n)
    (hi : Integrable (fun x => c x • rankMatrix (v x)) μ) (z : State n) :
    inner ℝ z (Matrix.toEuclideanCLM (𝕜 := ℝ) (profileCovariance μ c v) z) =
      ∫ x, c x * (inner ℝ z (v x)) ^ 2 ∂μ := by
  have hv := (matrixApply z).integrable_comp hi
  have hh := (innerSL ℝ z).integral_comp_comm hv
  rw [(matrixApply z).integral_comp_comm hi] at hh
  change (∫ x, (innerSL ℝ z) (matrixApply z (c x • rankMatrix (v x))) ∂μ) =
    inner ℝ z (Matrix.toEuclideanCLM (𝕜 := ℝ) (profileCovariance μ c v) z) at hh
  rw [← hh]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  simp only [map_smul, matrixApply_apply, rankMatrix_apply, innerSL_apply_apply,
    inner_smul_right]
  rw [real_inner_comm (v x) z]
  ring

end SHE.GaussianProfileMark
