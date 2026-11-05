module
public import SHE.GaussianCoordinates
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.GaussianDifferenceMap
open MeasureTheory ProbabilityTheory WordRecursion
open scoped RealInnerProductSpace
variable{n m:ℕ}

def difference(f g:Fin m→Fin n):State n→L[ℝ] State m:=
  GaussianCoordinates.projection f-GaussianCoordinates.projection g

/-- Subtracting the actual Gaussian baseline has the literal four-term
covariance, including singular ranks and repeated observations. -/
theorem map(f g:Fin m→Fin n){A:Matrix (Fin n) (Fin n) ℝ}(hA:A.PosSemidef)
    {B:Matrix (Fin m) (Fin m) ℝ}(hB:B.PosSemidef)
    (he:∀i j,B i j=A (f i) (f j)-A (f i) (g j)-A (g i) (f j)+A (g i) (g j)):
    (multivariateGaussian (0:State n) A).map (difference f g)=multivariateGaussian 0 B:=by
  apply IsGaussian.ext
  · simp only[id_eq,integral_id_multivariateGaussian]
    rw[ContinuousLinearMap.integral_id_map,integral_id_multivariateGaussian,map_zero]
    exact IsGaussian.integrable_id
  rw[←ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun (Fin m) ℝ).toBasis fun i j=>?_
  rw[ContinuousLinearMap.toBilinForm_apply,ContinuousLinearMap.toBilinForm_apply,
    covarianceBilin_apply_eq_cov,covariance_map]
  · have hh(i:Fin m):(fun u:State m=>⟪(EuclideanSpace.basisFun (Fin m) ℝ).toBasis i,u⟫)∘
        difference f g=(fun z:State n=>z (f i)-z (g i)):=by
      funext z
      simp[difference,PiLp.inner_apply]
    simp_rw[hh]
    have hm(k:Fin n):MemLp (fun z:State n=>z k) 2 (multivariateGaussian (0:State n) A):=
      ((IsGaussian.hasGaussianLaw_id (μ:=multivariateGaussian (0:State n) A)).map_fun
        (EuclideanSpace.proj k)).memLp_two
    rw[covariance_fun_sub_fun_sub (hm (f i)) (hm (g i)) (hm (f j)) (hm (g j))]
    simp_rw[covariance_eval_multivariateGaussian hA]
    rw[covarianceBilin_multivariateGaussian hB]
    simpa using (he i j).symm
  any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact IsGaussian.memLp_two_id
end SHE.GaussianDifferenceMap
