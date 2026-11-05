module

public import SHEStochastic.MatrixHaarAlgebra
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Measurable
public import Mathlib.Analysis.Matrix.MeasurableSpace

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.MatrixHaarMeasurability
open MeasureTheory MatrixHaarAlgebra
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The usual total nonsingular matrix inverse is Borel, including
singular masses. On positive definite masses it is the genuine inverse. -/
theorem measurable_inverse : Measurable (fun A : Matrix n n ℝ ↦ A⁻¹) := by
  have hd : Continuous (fun A : Matrix n n ℝ ↦ A.det) := continuous_id.matrix_det
  have ha : Continuous (fun A : Matrix n n ℝ ↦ A.adjugate) := continuous_id.matrix_adjugate
  apply Measurable.of_eval_matrix
  intro i j
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  exact hd.measurable.inv.mul (ha.measurable.eval_matrix (i := i) (j := j))

theorem measurable_normalizer :
    Measurable (fun p : Matrix n n ℝ × Matrix n n ℝ ↦ normalizer p.1 p.2) :=
  measurable_inverse.comp (CFC.measurable_sqrt.comp
    ((measurable_inverse.comp measurable_fst).add (measurable_inverse.comp measurable_snd)))

/-- Ordered left and right child coefficients can be evaluated on
random mass profiles without a separate matrix-selection assumption. -/
theorem measurable_children :
    Measurable (fun p : Matrix n n ℝ × Matrix n n ℝ ↦ (left p.1 p.2, right p.1 p.2)) :=
  ((measurable_inverse.comp measurable_fst).mul measurable_normalizer).prodMk
    (((measurable_inverse.comp measurable_snd).mul measurable_normalizer).neg)

end SHEStochastic.MatrixHaarMeasurability
