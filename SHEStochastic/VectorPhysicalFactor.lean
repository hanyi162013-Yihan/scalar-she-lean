module

public import SHEStochastic.VectorWhiteCoordinates
public import SHEStochastic.BoundedFieldOperator
public import SHE.SynthesisEquivalence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.VectorPhysicalFactor
open MeasureTheory SHE.FiniteHaar VectorWhiteCoordinates BoundedFieldOperator

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]

abbrev Coefficient := Field (AddCircle.haarAddCircle (T := (1 : ℝ)))
  (EuclideanSpace ℝ d) (EuclideanSpace ℝ d)

/-- An actual countable physical vector noise factor, built from a
bounded coefficient field and the proved vector white coordinates. -/
def factor (A : Coefficient (d := d)) : Input (d := d) →L[ℝ] Physical (d := d) :=
  (operator A).comp analysis.symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem single (A : Coefficient (d := d)) (p : d × HaarNode) :
    factor A (lp.single 2 p 1) = operator A (basis p) := by
  change operator A (analysis.symm (lp.single 2 p 1)) = _
  rw [VectorWhiteCoordinates.synthesis_single]

theorem column_ae (A : Coefficient (d := d)) (p : d × HaarNode) :
    ⇑(factor A (lp.single 2 p 1)) =ᵐ[AddCircle.haarAddCircle]
      fun x => A.value x (basis p x) := by
  rw [single]
  exact operator_ae A (basis p)

/-- Exact covariance on the physical vector Hilbert space, with all
cross-state terms retained. -/
theorem covariance (A : Coefficient (d := d)) :
    (factor A).comp (factor A).adjoint = operator (comp A (adjoint A)) := by
  let W := (analysis (d := d)).symm
  have hW : W.toContinuousLinearEquiv.toContinuousLinearMap.comp
      W.toContinuousLinearEquiv.toContinuousLinearMap.adjoint =
        ContinuousLinearMap.id ℝ (Physical (d := d)) := by
    rw [W.adjoint_eq_symm]
    apply ContinuousLinearMap.ext
    intro u
    exact W.apply_symm_apply u
  rw [operator_comp, operator_adjoint]
  change ((operator A).comp W.toContinuousLinearEquiv.toContinuousLinearMap).comp
    ((operator A).comp W.toContinuousLinearEquiv.toContinuousLinearMap).adjoint = _
  rw [ContinuousLinearMap.adjoint_comp]
  calc
    _ = ((operator A).comp
        (W.toContinuousLinearEquiv.toContinuousLinearMap.comp
          W.toContinuousLinearEquiv.toContinuousLinearMap.adjoint)).comp (operator A).adjoint := by
      simp only [ContinuousLinearMap.comp_assoc]
    _ = _ := by rw [hW, ContinuousLinearMap.comp_id]

theorem norm_bound (A : Coefficient (d := d)) (u : Input (d := d)) :
    ‖factor A u‖ ≤ (A.bound : ℝ)*‖u‖ := by
  exact (multiply_norm A (analysis.symm u)).trans_eq
    (congrArg (fun z : ℝ => (A.bound : ℝ)*z) (analysis.symm.norm_map u))

end SHEStochastic.VectorPhysicalFactor
