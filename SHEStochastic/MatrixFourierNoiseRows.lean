module

public import SHEStochastic.MatrixFourierCoordinates
public import SHEStochastic.MatrixStateNoise
public import SHEStochastic.MatrixSquareCoefficient

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
noncomputable section

namespace SHEStochastic.MatrixFourierNoiseRows
open MeasureTheory SHE MatrixInfiniteHaar MatrixFourierCoordinates
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {d : Type*} [Fintype d] [DecidableEq d]
local notation "ν" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable (G : MatrixNonlinearCoefficient.Coefficient d) {C β : ℝ≥0}
    (hG : HolderWith C β G.value) (hβ : 0 < β) (hβ1 : β ≤ 1)
    {P : Profile d} (A : MatrixSquareCoefficient.Data P) (u : Physical (d := d))
    (hA : A.value =ᵐ[ν] fun x => G.value (u x))

include hA in
/-- The native square coefficient's Fourier observation row is exactly
the fixed white-coordinate image of the literal state-dependent spatial row. -/
theorem factor_test (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    A.factor.adjoint (test i a n)=VectorWhiteCoordinates.analysis
      (MatrixStateNoise.row G hG hβ hβ1 i (weight a n) u) := by
  unfold MatrixSquareCoefficient.Data.factor VectorPhysicalFactor.factor
  rw [ContinuousLinearMap.adjoint_comp,
    (VectorWhiteCoordinates.analysis (d := d)).symm.adjoint_eq_symm,
    ← BoundedFieldOperator.operator_adjoint]
  change VectorWhiteCoordinates.analysis
      (BoundedFieldOperator.operator (BoundedFieldOperator.adjoint A.field) (test i a n))=_
  apply congrArg VectorWhiteCoordinates.analysis
  apply Lp.ext
  filter_upwards [BoundedFieldOperator.operator_ae (BoundedFieldOperator.adjoint A.field) (test i a n),
    test_ae i a n,MatrixStateNoise.row_ae G hG hβ hβ1 i (weight a n) u,hA]
    with x hop htest hrow hcoeff
  rw [hop,htest,hrow]
  change (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (A.value x)).adjoint
      (weight a n x • EuclideanSpace.single i (1 : ℝ))=_
  rw [map_smul,hcoeff]
  rfl

include hA in
/-- Analytic heat propagation gives the exact scalar Fourier decay in
every concrete matrix noise row. -/
theorem factor_heat (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ) {t : ℝ} (ht : 0 ≤ t) :
    A.factor.adjoint ((VectorAnalyticHeat.heat t).adjoint (test i a n))=
      Real.exp (-t*(n : ℝ)^2) • VectorWhiteCoordinates.analysis
        (MatrixStateNoise.row G hG hβ hβ1 i (weight a n) u) := by
  rw [adjoint_heat i a n ht,map_smul,factor_test G hG hβ hβ1 A u hA]

end SHEStochastic.MatrixFourierNoiseRows
