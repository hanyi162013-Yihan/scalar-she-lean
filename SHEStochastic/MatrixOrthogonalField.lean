module

public import SHEStochastic.MatrixFieldParameterAction

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixOrthogonalField
open MeasureTheory Matrix
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem action_norm (A : Matrix d d ℝ) (hA : Aᴴ*A=1) (v : EuclideanSpace ℝ d) :
    ‖Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) A v‖=‖v‖ := by
  have hs : (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) A).adjoint.comp
      (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) A)=ContinuousLinearMap.id ℝ _ := by
    change star (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) A)*Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) A=_
    rw [← map_star,← map_mul,Matrix.star_eq_conjTranspose,hA,map_one]
    rfl
  have hh := ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right
    (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) A) v
  rw [hs,ContinuousLinearMap.id_apply,real_inner_self_eq_norm_sq] at hh
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hh

theorem matrix_norm (A : Matrix d d ℝ) (hA : Aᴴ*A=1) : ‖A‖ ≤ 1 := by
  change ‖Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) A‖ ≤ 1
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [action_norm A hA,one_mul]

variable (Q : AddCircle (1 : ℝ) → Matrix d d ℝ) (hQ : Measurable Q)
  (hCol : ∀ᵐ x ∂AddCircle.haarAddCircle (T := (1 : ℝ)), (Q x)ᴴ*Q x=1)

def field : BoundedFieldOperator.Field (AddCircle.haarAddCircle (T := (1 : ℝ)))
    (EuclideanSpace ℝ d) (EuclideanSpace ℝ d) :=
  MatrixFieldOperator.field Q hQ 1 (hCol.mono fun x hx => matrix_norm _ hx)

def operator : MatrixInfiniteHaar.Physical (d := d) →L[ℝ] MatrixInfiniteHaar.Physical (d := d) :=
  BoundedFieldOperator.operator (field Q hQ hCol)

theorem norm_map (u : MatrixInfiniteHaar.Physical (d := d)) : ‖operator Q hQ hCol u‖=‖u‖ := by
  have hh : inner ℝ (operator Q hQ hCol u) (operator Q hQ hCol u)=inner ℝ u u := by
    rw [L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [BoundedFieldOperator.operator_ae (field Q hQ hCol) u,hCol] with x hx hc
    change inner ℝ (BoundedFieldOperator.operator (field Q hQ hCol) u x)
      (BoundedFieldOperator.operator (field Q hQ hCol) u x)=inner ℝ (u x) (u x)
    rw [hx]
    change inner ℝ (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (Q x) (u x))
      (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (Q x) (u x))=inner ℝ (u x) (u x)
    rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,action_norm (Q x) hc]
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at hh
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hh

def star_measurable : Measurable (fun x => (Q x)ᴴ) := continuous_star.measurable.comp hQ

include hCol in
theorem star_columns : ∀ᵐ x ∂AddCircle.haarAddCircle (T := (1 : ℝ)),
    ((Q x)ᴴ)ᴴ*(Q x)ᴴ=1 := hCol.mono fun x hx => by
  rw [Matrix.conjTranspose_conjTranspose]
  exact mul_eq_one_comm.mp hx

/-- A pointwise orthogonal matrix field induces a genuine unitary on
the full vector spatial Hilbert space, with inverse its transpose field. -/
def equivalence : MatrixInfiniteHaar.Physical (d := d) ≃ₗᵢ[ℝ] MatrixInfiniteHaar.Physical (d := d) := by
  let A := field Q hQ hCol
  let B := field (fun x => (Q x)ᴴ) (star_measurable Q hQ) (star_columns Q hCol)
  have hBA : ∀ᵐ x ∂AddCircle.haarAddCircle (T := (1 : ℝ)),
      (B.value x).comp (A.value x)=ContinuousLinearMap.id ℝ _ := by
    filter_upwards [hCol] with x hx
    change (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (Q x)ᴴ)*Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (Q x)=_
    rw [← map_mul,hx,map_one]
    rfl
  have hAB : ∀ᵐ x ∂AddCircle.haarAddCircle (T := (1 : ℝ)),
      (A.value x).comp (B.value x)=ContinuousLinearMap.id ℝ _ := by
    filter_upwards [hCol] with x hx
    change (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (Q x))*Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (Q x)ᴴ=_
    rw [← map_mul,mul_eq_one_comm.mp hx,map_one]
    rfl
  let e := BoundedFieldOperator.equivalence A B hBA hAB
  exact LinearIsometryEquiv.ofSurjective
    { (operator Q hQ hCol).toLinearMap with norm_map' := norm_map Q hQ hCol } e.surjective

theorem equivalence_apply (u : MatrixInfiniteHaar.Physical (d := d)) :
    equivalence Q hQ hCol u=operator Q hQ hCol u := rfl

/-- The inverse of the spatial orthogonal action is the actual
transpose-matrix field operator on physical L². -/
theorem equivalence_symm_apply (u : MatrixInfiniteHaar.Physical (d := d)) :
    (equivalence Q hQ hCol).symm u =
      operator (fun x => (Q x)ᴴ) (star_measurable Q hQ) (star_columns Q hCol) u := by
  have hAB : ∀ᵐ x ∂AddCircle.haarAddCircle (T := (1 : ℝ)),
      ((field Q hQ hCol).value x).comp
        ((field (fun x => (Q x)ᴴ) (star_measurable Q hQ)
          (star_columns Q hCol)).value x) = ContinuousLinearMap.id ℝ _ := by
    filter_upwards [hCol] with x hx
    change (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (Q x))*
      Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (Q x)ᴴ=_
    rw [← map_mul,mul_eq_one_comm.mp hx,map_one]
    rfl
  apply (equivalence Q hQ hCol).injective
  rw [LinearIsometryEquiv.apply_symm_apply,equivalence_apply]
  change u = (BoundedFieldOperator.operator (field Q hQ hCol))
    ((BoundedFieldOperator.operator (field (fun x => (Q x)ᴴ)
      (star_measurable Q hQ) (star_columns Q hCol))) u)
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using
    (congrArg (fun T : MatrixInfiniteHaar.Physical (d := d) →L[ℝ]
      MatrixInfiniteHaar.Physical (d := d) => T u)
      (BoundedFieldOperator.operator_inverse
        (field (fun x => (Q x)ᴴ) (star_measurable Q hQ) (star_columns Q hCol))
        (field Q hQ hCol) hAB)).symm

section Parameters
variable {Z : Type*} [MeasurableSpace Z]
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology (MatrixInfiniteHaar.Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (MatrixInfiniteHaar.Physical (d := d)) := borel _
local instance : BorelSpace (MatrixInfiniteHaar.Physical (d := d)) := ⟨rfl⟩

theorem action (R : Z → AddCircle (1 : ℝ) → Matrix d d ℝ)
    (hR : Measurable (fun p : Z × AddCircle (1 : ℝ) => R p.1 p.2))
    (hOrth : ∀ z, ∀ᵐ x ∂AddCircle.haarAddCircle (T := (1 : ℝ)), (R z x)ᴴ*R z x=1)
    (u : Z → MatrixInfiniteHaar.Physical (d := d)) (hu : Measurable u) :
    Measurable (fun z => equivalence (R z)
      (hR.comp (measurable_const.prodMk measurable_id)) (hOrth z) (u z)) := by
  change Measurable (fun z => MatrixFieldOperator.operator (R z)
    (hR.comp (measurable_const.prodMk measurable_id)) 1
    ((hOrth z).mono fun x hx => matrix_norm _ hx) (u z))
  exact MatrixFieldParameterAction.action R hR _ (fun _ => 1) _ u hu

end Parameters

end SHEStochastic.MatrixOrthogonalField
