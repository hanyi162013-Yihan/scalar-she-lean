module

public import SHE.GaussianCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.GaussianCoordinateRange
open Set MeasureTheory ProbabilityTheory WordRecursion GaussianCoordinates
open scoped BigOperators
variable {n m : ℕ}

def lift (f : Fin m → Fin n) (v : State m) : State n :=
  ∑ j, v j • EuclideanSpace.basisFun (Fin n) ℝ (f j)

theorem matrix_lift_apply (A : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin m → Fin n) (v : State m) (i : Fin n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) A (lift f v) i = ∑ j, A i (f j) * v j := by
  change (EuclideanSpace.proj i) (Matrix.toEuclideanCLM (𝕜 := ℝ) A (lift f v)) = _
  simp only [lift, map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  have he : Matrix.toEuclideanCLM (𝕜 := ℝ) A
      (EuclideanSpace.basisFun (Fin n) ℝ (f j)) i = A i (f j) := by
    change ∑ k, A i k * EuclideanSpace.basisFun (Fin n) ℝ (f j) k = A i (f j)
    simp
  exact (congrArg (fun r : ℝ => v j * r) he).trans (mul_comm _ _)

/-- A native physical direction in the range of the selected principal
covariance lifts to the full original observation space when all omitted
rows and direction coordinates are zero. Neither PSD nor injectivity is
needed for this exact linear algebra fact. -/
theorem range_lift (A : Matrix (Fin n) (Fin n) ℝ) (f : Fin m → Fin n) (d : State n)
    (hrows : ∀ i, i ∉ Set.range f → ∀ j, A i j = 0)
    (hd : ∀ i, i ∉ Set.range f → d i = 0)
    (hrange : projection f d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (A.submatrix f f)).range) :
    d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) A).range := by
  obtain ⟨v,hv⟩ := hrange
  refine ⟨lift f v, ?_⟩
  ext i
  apply (matrix_lift_apply A f v i).trans
  by_cases hi : i ∈ Set.range f
  · obtain ⟨j,rfl⟩ := hi
    have h := congrArg (fun z : State m => z j) hv
    exact h
  · simp only [hrows i hi, zero_mul, Finset.sum_const_zero, hd i hi]

end SHE.GaussianCoordinateRange
