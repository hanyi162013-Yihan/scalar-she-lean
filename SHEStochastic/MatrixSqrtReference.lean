module

public import SHEStochastic.MatrixHaarCovarianceInverse
public import SHEStochastic.VectorPhysicalFactor

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixSqrtReference
open MeasureTheory Matrix MatrixInfiniteHaar
open scoped NNReal MatrixOrder Matrix.Norms.L2Operator
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem sqrt_norm_sq (A : Matrix d d ℝ) (hA : 0 ≤ A) : ‖CFC.sqrt A‖^2=‖A‖ := by
  have hh : ‖star (CFC.sqrt A)*CFC.sqrt A‖=‖CFC.sqrt A‖*‖CFC.sqrt A‖ :=
    CStarRing.norm_star_mul_self
  simpa only [(CFC.sqrt_nonneg A).star_eq, CFC.sqrt_mul_sqrt_self A hA, ← pow_two] using hh.symm

theorem nonnegative (P : Profile d) :
    ∀ᵐ x ∂AddCircle.haarAddCircle (T := (1 : ℝ)), 0 ≤ P.value x := by
  filter_upwards [P.lower_bound] with x hx
  exact le_trans (smul_nonneg P.lower_pos.le zero_le_one) hx

theorem sqrt_bound (P : Profile d) :
    ∀ᵐ x ∂AddCircle.haarAddCircle (T := (1 : ℝ)), ‖CFC.sqrt (P.value x)‖ ≤ NNReal.sqrt P.bound := by
  filter_upwards [nonnegative P, P.norm_bound] with x hx hb
  have hs := sqrt_norm_sq (P.value x) hx
  have he : ((NNReal.sqrt P.bound : ℝ))^2=(P.bound : ℝ) := by
    exact_mod_cast NNReal.sq_sqrt P.bound
  exact (sq_le_sq₀ (norm_nonneg _) (NNReal.coe_nonneg _)).mp (by rw [hs, he]; exact hb)

/-- The standard positive matrix square root acts on the actual vector
spatial Hilbert space with its derived uniform bound. -/
def field (P : Profile d) : VectorPhysicalFactor.Coefficient (d := d) :=
  MatrixFieldOperator.field (fun x => CFC.sqrt (P.value x)) (CFC.measurable_sqrt.comp P.measurable)
    (NNReal.sqrt P.bound) (sqrt_bound P)

def operator (P : Profile d) : Physical (d := d) →L[ℝ] Physical (d := d) :=
  BoundedFieldOperator.operator (field P)

theorem square (P : Profile d) : (operator P).comp (operator P)=multiplier P := by
  rw [operator, ← BoundedFieldOperator.operator_comp]
  apply BoundedFieldOperator.operator_congr
  filter_upwards [nonnegative P] with x hx
  change (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)) (CFC.sqrt (P.value x)) *
    (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)) (CFC.sqrt (P.value x))=
      (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)) (P.value x)
  rw [← map_mul, CFC.sqrt_mul_sqrt_self _ hx]

theorem selfadjoint (P : Profile d) : (operator P).adjoint=operator P :=
  MatrixFieldAdjoint.selfadjoint _ (CFC.measurable_sqrt.comp P.measurable)
    (NNReal.sqrt P.bound) (sqrt_bound P)
    (Filter.Eventually.of_forall (fun x => (CFC.sqrt_nonneg (P.value x)).posSemidef.isHermitian))

theorem bijective (P : Profile d) : Function.Bijective (operator P) := by
  have hM := MatrixHaarCovarianceInverse.bijective P
  constructor
  · intro x y hxy
    apply hM.1
    have hh := congrArg (operator P) hxy
    change (operator P).comp (operator P) x=(operator P).comp (operator P) y at hh
    rwa [square] at hh
  · intro y
    obtain ⟨x, hx⟩ := hM.2 y
    refine ⟨operator P x, ?_⟩
    change (operator P).comp (operator P) x=y
    rwa [square]

def factor (P : Profile d) : Input (d := d) →L[ℝ] Physical (d := d) :=
  VectorPhysicalFactor.factor (field P)

theorem covariance (P : Profile d) : (factor P).comp (factor P).adjoint=multiplier P := by
  rw [factor, VectorPhysicalFactor.covariance, BoundedFieldOperator.operator_comp,
    BoundedFieldOperator.operator_adjoint]
  change (operator P).comp (operator P).adjoint=_
  rw [selfadjoint, square]

end SHEStochastic.MatrixSqrtReference
