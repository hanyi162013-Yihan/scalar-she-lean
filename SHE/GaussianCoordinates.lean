module

public import SHE.SmoothWords

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.GaussianCoordinates
open Set MeasureTheory ProbabilityTheory WordRecursion
open scoped RealInnerProductSpace
variable {n m : ℕ}

/-- Select original coordinates, allowing repeated coordinates. -/
def projection (f : Fin m → Fin n) : State n →L[ℝ] State m :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 (fun i => z (f i))
      map_add' := by intros; ext i; rfl
      map_smul' := by intros; ext i; rfl }

@[simp] theorem projection_apply (f : Fin m → Fin n) (z : State n) (i : Fin m) :
    projection f z i = z (f i) := rfl

/-- The covariance of a projected singular Gaussian is the literal
submatrix on the selected observations. No invertibility is needed. -/
theorem measurePreserving_projection (f : Fin m → Fin n) (μ : State n)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) :
    MeasurePreserving (projection f) (multivariateGaussian μ A)
      (multivariateGaussian (projection f μ) (A.submatrix f f)) where
  measurable := (projection f).measurable
  map_eq := by
    apply IsGaussian.ext
    · simp only [id_eq, integral_id_multivariateGaussian]
      rw [ContinuousLinearMap.integral_id_map, integral_id_multivariateGaussian]
      exact IsGaussian.integrable_id
    rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun (Fin m) ℝ).toBasis fun i j => ?_
    rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
      covarianceBilin_apply_eq_cov, covariance_map]
    · have he (i : Fin m) : (fun u => ⟪(EuclideanSpace.basisFun (Fin m) ℝ).toBasis i, u⟫) ∘
          projection f = fun u => u (f i) := by
        ext u
        simp [PiLp.inner_apply]
      simp_rw [he, covariance_eval_multivariateGaussian hA,
        covarianceBilin_multivariateGaussian (hA.submatrix f)]
      simp
    any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
    · fun_prop
    · exact IsGaussian.memLp_two_id

/-- Gaussian averaging commutes with selecting the original coordinates,
including the growing word's tail projection. -/
theorem average_projection (f : Fin m → Fin n)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (F : State m → ℝ) (hF : Measurable F) (z : State n) :
    GaussianConvolution.gaussianAverage A (fun x => F (projection f x)) z =
      GaussianConvolution.gaussianAverage (A.submatrix f f) F (projection f z) := by
  have h := integral_map (μ := multivariateGaussian (0 : State n) A)
    (φ := projection f) (f := fun x => F (projection f z + x))
    (projection f).measurable.aemeasurable
    (hF.comp (measurable_const.add measurable_id)).aestronglyMeasurable
  rw [(measurePreserving_projection f (0 : State n) hA).map_eq] at h
  simpa only [map_zero, GaussianConvolution.gaussianAverage, map_add] using h.symm

end SHE.GaussianCoordinates
