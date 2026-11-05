module

public import SHEStochastic.BoundedFieldOperator
public import SHEStochastic.MatrixHaarMeasurability
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.MatrixFieldOperator
open MeasureTheory BoundedFieldOperator Matrix
open scoped NNReal Matrix.Norms.L2Operator

variable {X d : Type*} [MeasurableSpace X] {μ : Measure X} [Fintype d] [DecidableEq d]

abbrev Physical := Lp (EuclideanSpace ℝ d) 2 μ

/-- A bounded measurable matrix coefficient acts by its literal matrix
product on the vector-valued spatial `L²` space. -/
def field (κ : X → Matrix d d ℝ) (hκ : Measurable κ) (B : ℝ≥0)
    (hB : ∀ᵐ x ∂μ, ‖κ x‖ ≤ B) : Field μ (EuclideanSpace ℝ d) (EuclideanSpace ℝ d) where
  value x := (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)) (κ x)
  measurable := (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.continuous.comp_aestronglyMeasurable
    hκ.aestronglyMeasurable
  bound := B
  norm_bound := by
    filter_upwards [hB] with x hx
    exact (Matrix.cstar_norm_def (κ x)).ge.trans hx

def operator (κ : X → Matrix d d ℝ) (hκ : Measurable κ) (B : ℝ≥0)
    (hB : ∀ᵐ x ∂μ, ‖κ x‖ ≤ B) : Physical (d := d) (μ := μ) →L[ℝ] Physical (d := d) (μ := μ) :=
  BoundedFieldOperator.operator (field κ hκ B hB)

theorem operator_ae (κ : X → Matrix d d ℝ) (hκ : Measurable κ) (B : ℝ≥0)
    (hB : ∀ᵐ x ∂μ, ‖κ x‖ ≤ B) (u : Physical (d := d) (μ := μ)) :
    ∀ᵐ x ∂μ, (operator κ hκ B hB u x).ofLp = κ x *ᵥ (u x).ofLp := by
  filter_upwards [BoundedFieldOperator.operator_ae (field κ hκ B hB) u] with x hx
  exact congrArg WithLp.ofLp hx

theorem inverse_left (κ : X → Matrix d d ℝ) (hκ : Measurable κ) (B C : ℝ≥0)
    (hB : ∀ᵐ x ∂μ, ‖κ x‖ ≤ B) (hC : ∀ᵐ x ∂μ, ‖(κ x)⁻¹‖ ≤ C)
    (hu : ∀ᵐ x ∂μ, IsUnit (κ x)) :
    (operator (fun x => (κ x)⁻¹) (MatrixHaarMeasurability.measurable_inverse.comp hκ) C hC).comp
      (operator κ hκ B hB) = ContinuousLinearMap.id ℝ (Physical (d := d) (μ := μ)) := by
  apply BoundedFieldOperator.operator_inverse
  filter_upwards [hu] with x hx
  change (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)) ((κ x)⁻¹) * (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)) (κ x) = _
  rw [← map_mul]
  have hm : (κ x)⁻¹ * κ x = 1 := by
    letI := hx.invertible
    exact Matrix.inv_mul_of_invertible _
  rw [hm, map_one]
  rfl

theorem inverse_right (κ : X → Matrix d d ℝ) (hκ : Measurable κ) (B C : ℝ≥0)
    (hB : ∀ᵐ x ∂μ, ‖κ x‖ ≤ B) (hC : ∀ᵐ x ∂μ, ‖(κ x)⁻¹‖ ≤ C)
    (hu : ∀ᵐ x ∂μ, IsUnit (κ x)) :
    (operator κ hκ B hB).comp
      (operator (fun x => (κ x)⁻¹) (MatrixHaarMeasurability.measurable_inverse.comp hκ) C hC) =
        ContinuousLinearMap.id ℝ (Physical (d := d) (μ := μ)) := by
  apply BoundedFieldOperator.operator_inverse
  filter_upwards [hu] with x hx
  change (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)) (κ x) * (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)) ((κ x)⁻¹) = _
  rw [← map_mul]
  have hm : κ x * (κ x)⁻¹ = 1 := by
    letI := hx.invertible
    exact Matrix.mul_inv_of_invertible _
  rw [hm, map_one]
  rfl

end SHEStochastic.MatrixFieldOperator
