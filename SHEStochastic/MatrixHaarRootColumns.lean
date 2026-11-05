module

public import SHEStochastic.MatrixHaarLpColumns
public import SHEStochastic.MatrixFiniteHaar

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixHaarRootColumns
open MeasureTheory Matrix MatrixHaarFunctions
open scoped NNReal Matrix.Norms.L2Operator

variable {d X : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]

def column (C : Matrix d d ℝ) (i : d) : EuclideanSpace ℝ d :=
  Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) C (EuclideanSpace.single i 1)

def columnMap (i : d) : Matrix d d ℝ →L[ℝ] EuclideanSpace ℝ d :=
  (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ d) (EuclideanSpace.single i 1)).comp
    (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem columnMap_apply (i : d) (C : Matrix d d ℝ) : columnMap i C=column C i := rfl

theorem column_mul (C D : Matrix d d ℝ) (i : d) :
    column (C*D) i=Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) C (column D i) := by
  change (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)) (C*D) (EuclideanSpace.single i 1) = _
  rw [map_mul]
  rfl

theorem column_apply (C : Matrix d d ℝ) (i p : d) : column C i p = C p i := by
  simp [column, Matrix.mulVec, dotProduct]

theorem inner_columns (C K D : Matrix d d ℝ) (i j : d) :
    inner ℝ (column C i) (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) K (column D j)) =
      (Cᴴ*K*D) i j := by
  rw [Matrix.inner_toEuclideanCLM, MatrixHaarLpColumns.cross_entry]
  simp only [dotProduct, Matrix.mulVec, column_apply]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  ring

def constant (C : Matrix d d ℝ) (i : d) : Lp (EuclideanSpace ℝ d) 2 μ :=
  (memLp_const (μ := μ) (p := 2) (column C i)).toLp (fun _ => column C i)

theorem constant_ae (C : Matrix d d ℝ) (i : d) :
    ⇑(constant μ C i) =ᵐ[μ] fun _ => column C i := (memLp_const (μ := μ) (p := 2) (column C i)).coeFn_toLp

/-- The root pairing is computed against the actual total covariance
mass, not a finite-grid substitute. -/
theorem pairing (κ : X → Matrix d d ℝ) (hκ : Measurable κ) (hInt : Integrable κ μ)
    (B : ℝ≥0) (hBound : ∀ᵐ x ∂μ, ‖κ x‖ ≤ B) (C D : Matrix d d ℝ) (i j : d) :
    inner ℝ (constant μ C i) (MatrixFieldOperator.operator κ hκ B hBound (constant μ D j)) =
      (Cᴴ*(∫ x, κ x ∂μ)*D) i j := by
  rw [L2.inner_def]
  have hCross := (hInt.const_mul Cᴴ).mul_const D
  have hh := (MatrixHaarPairings.entry i j).integral_comp_comm hCross
  change (∫ x, (Cᴴ*κ x*D) i j ∂μ) = _ at hh
  have he : (∫ x, Cᴴ*κ x*D ∂μ) = Cᴴ*(∫ x, κ x ∂μ)*D := by
    rw [integral_mul_const_of_integrable (hInt.const_mul Cᴴ), integral_const_mul_of_integrable hInt]
  rw [he] at hh
  apply Eq.trans _ hh
  apply integral_congr_ae
  filter_upwards [constant_ae μ C i, constant_ae μ D j,
    BoundedFieldOperator.operator_ae (MatrixFieldOperator.field κ hκ B hBound) (constant μ D j)] with x hc hd hm
  rw [hc]
  change inner ℝ (column C i)
    (BoundedFieldOperator.operator (MatrixFieldOperator.field κ hκ B hBound) (constant μ D j) x) = _
  rw [hm, hd]
  exact inner_columns C (κ x) D i j

def root (κ : X → Matrix d d ℝ) (i : d) : Lp (EuclideanSpace ℝ d) 2 μ :=
  constant μ (MatrixFiniteHaar.inverseSqrt (∫ x, κ x ∂μ)) i

/-- The actual root vectors have the Kronecker weighted Gram matrix. -/
theorem weighted_gram (κ : X → Matrix d d ℝ) (hκ : Measurable κ) (hInt : Integrable κ μ)
    (B : ℝ≥0) (hBound : ∀ᵐ x ∂μ, ‖κ x‖ ≤ B)
    (hp : (∫ x, κ x ∂μ).PosDef) (i j : d) :
    inner ℝ (root μ κ i) (MatrixFieldOperator.operator κ hκ B hBound (root μ κ j)) =
      if i=j then 1 else 0 := by
  rw [root, root, pairing μ κ hκ hInt B hBound, MatrixFiniteHaar.inverseSqrt_gram _ hp]
  exact Matrix.one_apply


/-- Every detail block has zero weighted pairing with every constant
vector block, including the actual root. -/
theorem constant_detail (κ : X → Matrix d d ℝ) (hκ : Measurable κ) (hInt : Integrable κ μ)
    (B : ℝ≥0) (hBound : ∀ᵐ x ∂μ, ‖κ x‖ ≤ B) (C : Matrix d d ℝ)
    (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hA : (mass μ κ s).PosDef) (hB : (mass μ κ t).PosDef) (i j : d) :
    inner ℝ (constant μ C i)
      (MatrixFieldOperator.operator κ hκ B hBound (MatrixHaarLpColumns.vector μ κ s t hs ht j)) = 0 := by
  let Q := fun x => MatrixHaarFunctions.column μ κ s t x
  have hin := MatrixHaarFunctions.integrable_weighted μ κ hInt s t hs ht
  have hh := (MatrixHaarPairings.entry i j).integral_comp_comm (hin.const_mul Cᴴ)
  change (∫ x, (Cᴴ*(κ x*Q x)) i j ∂μ) = _ at hh
  rw [integral_const_mul_of_integrable hin, MatrixHaarFunctions.weighted_mean μ κ hInt s t hs ht hA hB,
    Matrix.mul_zero] at hh
  change (∫ x, (Cᴴ*(κ x*Q x)) i j ∂μ) = 0 at hh
  rw [L2.inner_def]
  apply Eq.trans _ hh
  apply integral_congr_ae
  filter_upwards [constant_ae μ C i, MatrixHaarLpColumns.vector_ae μ κ s t hs ht j,
    BoundedFieldOperator.operator_ae (MatrixFieldOperator.field κ hκ B hBound)
      (MatrixHaarLpColumns.vector μ κ s t hs ht j)] with x hc hv hm
  rw [hc]
  change inner ℝ (column C i)
    (BoundedFieldOperator.operator (MatrixFieldOperator.field κ hκ B hBound)
      (MatrixHaarLpColumns.vector μ κ s t hs ht j) x) = _
  rw [hm, hv]
  change inner ℝ (column C i)
    (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (κ x) (column (Q x) j)) = _
  simpa only [Matrix.mul_assoc] using inner_columns C (κ x) (Q x) i j

end SHEStochastic.MatrixHaarRootColumns
