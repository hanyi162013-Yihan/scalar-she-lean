module

public import SHEStochastic.MatrixFieldQuadratic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.MatrixFieldAdjoint
open MeasureTheory Matrix
open scoped NNReal MatrixOrder Matrix.Norms.L2Operator
variable {d X : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace X] {μ : Measure X}

theorem selfadjoint (κ : X → Matrix d d ℝ) (hκ : Measurable κ)
    (B : ℝ≥0) (hB : ∀ᵐ x ∂μ, ‖κ x‖ ≤ B) (hHerm : ∀ᵐ x ∂μ, (κ x).IsHermitian) :
    (MatrixFieldOperator.operator κ hκ B hB).adjoint=MatrixFieldOperator.operator κ hκ B hB := by
  change (BoundedFieldOperator.operator (MatrixFieldOperator.field κ hκ B hB)).adjoint=_
  rw [← BoundedFieldOperator.operator_adjoint]
  apply BoundedFieldOperator.operator_congr
  filter_upwards [hHerm] with x hx
  change star ((Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)) (κ x))=
    (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)) (κ x)
  rw [← map_star]
  exact congrArg (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)) hx.eq

theorem selfadjoint_of_elliptic (κ : X → Matrix d d ℝ) (hκ : Measurable κ)
    (B : ℝ≥0) (hB : ∀ᵐ x ∂μ, ‖κ x‖ ≤ B) (m : ℝ) (hm : 0 < m)
    (hLo : ∀ᵐ x ∂μ, m • (1 : Matrix d d ℝ) ≤ κ x) :
    (MatrixFieldOperator.operator κ hκ B hB).adjoint=MatrixFieldOperator.operator κ hκ B hB := by
  apply selfadjoint κ hκ B hB
  filter_upwards [hLo] with x hx
  exact (le_trans (smul_nonneg hm.le zero_le_one) hx).posSemidef.isHermitian

end SHEStochastic.MatrixFieldAdjoint
