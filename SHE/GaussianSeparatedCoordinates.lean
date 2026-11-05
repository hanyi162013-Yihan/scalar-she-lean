module
public import SHE.GaussianCoordinates
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Independence.Integration

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.GaussianSeparatedCoordinates
open Set MeasureTheory ProbabilityTheory WordRecursion GaussianCoordinates
open scoped NNReal ENNReal
variable {n a b:ℕ} (f:Fin a→Fin n) (g:Fin b→Fin n)
variable {A:Matrix (Fin n) (Fin n) ℝ} (hA:A.PosSemidef)
variable (hc:∀i j,A (f i) (g j)=0)

include hA hc in
/-- True zero cross covariance of two coordinate blocks of a singular
Gaussian implies their independence. No residual-residual independence
is imposed within either block. -/
theorem independent:IndepFun (projection f) (projection g) (multivariateGaussian (0:State n) A):=by
  let L:State n→L[ℝ](Fin a→ℝ):=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _:Fin a=>ℝ)).toContinuousLinearMap.comp (projection f)
  let K:State n→L[ℝ](Fin b→ℝ):=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _:Fin b=>ℝ)).toContinuousLinearMap.comp (projection g)
  have hj:HasGaussianLaw (fun z:State n=>(L z,K z)) (multivariateGaussian 0 A):=
    (IsGaussian.hasGaussianLaw_id (μ:=multivariateGaussian (0:State n) A)).map_fun (L.prod K)
  have hi:IndepFun (fun z:State n=>fun i:Fin a=>z (f i))
      (fun z:State n=>fun j:Fin b=>z (g j)) (multivariateGaussian 0 A):=by
    apply HasGaussianLaw.indepFun_of_covariance_eval hj
    intro i j
    change cov[fun z:State n=>z (f i),fun z:State n=>z (g j);multivariateGaussian 0 A]=0
    rw [covariance_eval_multivariateGaussian hA]
    exact hc i j
  convert! hi.comp (WithLp.measurable_toLp 2 (Fin a→ℝ))
    (WithLp.measurable_toLp 2 (Fin b→ℝ)) using 1

include hA hc in
/-- Exact bounded-test Gaussian block factorization using the literal
submatrices, including all singular ranks. -/
theorem integral_product (F:State a×State b→ℝ) (hF:Measurable F)
    {M:ℝ} (hb:∀z,|F z|≤M):
    (∫z:State n,F (projection f z,projection g z) ∂multivariateGaussian 0 A)=
      ∫x:State a,∫y:State b,F (x,y) ∂multivariateGaussian 0 (A.submatrix g g)
        ∂multivariateGaussian 0 (A.submatrix f f):=by
  have hi:=independent f g hA hc
  have he:=hi.map_prod_eq_prod_map_map (projection f).measurable.aemeasurable
    (projection g).measurable.aemeasurable
  rw [(measurePreserving_projection f (0:State n) hA).map_eq,
    (measurePreserving_projection g (0:State n) hA).map_eq,map_zero,map_zero] at he
  have hp:Measurable (fun z:State n=>(projection f z,projection g z)):=
    (projection f).measurable.prodMk (projection g).measurable
  rw [←integral_map hp.aemeasurable hF.aestronglyMeasurable,he]
  apply integral_prod
  apply (integrable_const M).mono' hF.aestronglyMeasurable
  exact ae_of_all _ (fun z=>by simpa only [Real.norm_eq_abs] using hb z)

end SHE.GaussianSeparatedCoordinates
