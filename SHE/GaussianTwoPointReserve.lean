module
public import SHE.GaussianConvolution
public import SHE.NativeFirstWordRepresentation
public import SHE.ScalarGaussianSemigroup
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Independence.Integration

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.GaussianTwoPointReserve
open Set MeasureTheory ProbabilityTheory GaussianConvolution WordRecursion ScalarGaussianSemigroup
open scoped NNReal ENNReal

def covariance(v:ℝ≥0):Matrix (Fin 2) (Fin 2) ℝ:=Matrix.diagonal (fun _=>(v:ℝ))

theorem positive(v:ℝ≥0):(covariance v).PosSemidef:=
  Matrix.PosSemidef.diagonal (fun _=>v.2)

/-- The two original coordinates of the split scalar Gaussian reserve
are independent; independence follows from its actual diagonal law. -/
theorem independent(v:ℝ≥0):IndepFun (fun z:State 2=>z 0) (fun z:State 2=>z 1)
    (multivariateGaussian 0 (covariance v)):=by
  have hj:HasGaussianLaw (fun z:State 2=>(z 0,z 1)) (multivariateGaussian 0 (covariance v)):=by
    convert! (show HasGaussianLaw (fun z:State 2=>((EuclideanSpace.proj (0:Fin 2)) z,(EuclideanSpace.proj (1:Fin 2)) z))
      (multivariateGaussian 0 (covariance v)) from
      (IsGaussian.hasGaussianLaw_id (μ:=multivariateGaussian (0:State 2) (covariance v))).map_fun
        ((EuclideanSpace.proj (0:Fin 2)).prod (EuclideanSpace.proj (1:Fin 2)))) using 1
  apply hj.indepFun_of_covariance_eq_zero
  rw [covariance_eval_multivariateGaussian (positive v)]
  simp [covariance,Matrix.diagonal]


/-- Exact scalar factorization of the genuine two-dimensional reserve.
No nonsingularity or density formula is used, including at v=0. -/
theorem product(v:ℝ≥0)(f g:ℝ→ℝ)(hf:Measurable f)(hg:Measurable g)(m:State 2):
    gaussianAverage (covariance v) (fun z=>f (z 0)*g (z 1)) m=
      heat v f (m 0)*heat v g (m 1):=by
  have hi:IndepFun (fun z:State 2=>f (m 0+z 0)) (fun z:State 2=>g (m 1+z 1))
      (multivariateGaussian 0 (covariance v)):=
    (independent v).comp (hf.comp (measurable_const.add measurable_id))
      (hg.comp (measurable_const.add measurable_id))
  change (∫z:State 2,f (m 0+z 0)*g (m 1+z 1) ∂multivariateGaussian 0 (covariance v))=_
  rw [hi.integral_fun_mul_eq_mul_integral
    (hf.comp (measurable_const.add (EuclideanSpace.proj (0:Fin 2)).measurable)).aestronglyMeasurable
    (hg.comp (measurable_const.add (EuclideanSpace.proj (1:Fin 2)).measurable)).aestronglyMeasurable,
    NativeFirstWordRepresentation.coordinate_average (positive v) 0 f hf,
    NativeFirstWordRepresentation.coordinate_average (positive v) 1 g hg]
  simp only [covariance,Matrix.diagonal_apply_eq,Real.toNNReal_coe]
  rfl

/-- Split a common two-point Gaussian off any remaining correlated
Gaussian law. This is the exact covariance decomposition used before
spatial cancellation of the actual frozen-reference band difference. -/
theorem split {C:Matrix (Fin 2) (Fin 2) ℝ}(hC:C.PosSemidef)(v:ℝ≥0)
    (f g:ℝ→ℝ)(hf:Measurable f)(hg:Measurable g){Bf Bg:ℝ}
    (hBf:0≤Bf)(hBg:0≤Bg)(hfb:∀x,|f x|≤Bf)(hgb:∀x,|g x|≤Bg)(m:State 2):
    gaussianAverage (C+covariance v) (fun z=>f (z 0)*g (z 1)) m=
      gaussianAverage C (fun z=>heat v f (z 0)*heat v g (z 1)) m:=by
  have hF:Measurable (fun z:State 2=>f (z 0)*g (z 1)):=by fun_prop
  have hb(z:State 2):|f (z 0)*g (z 1)|≤Bf*Bg:=by
    rw [abs_mul]
    exact mul_le_mul (hfb _) (hgb _) (abs_nonneg _) hBf
  rw [←gaussianAverage_composition C (covariance v) hC (positive v) _ hF hb]
  exact congrArg (fun F=>gaussianAverage C F m) (funext (product v f g hf hg))

/-- Pointwise polynomial scalar heat bounds control the original
correlated two-point Gaussian expectation after the exact reserve split. -/
theorem bound {C:Matrix (Fin 2) (Fin 2) ℝ}(hC:C.PosSemidef)(v:ℝ≥0)
    (f g:ℝ→ℝ)(hf:Measurable f)(hg:Measurable g){Bf Bg Uf Ug:ℝ}
    (hBf:0≤Bf)(hBg:0≤Bg)(hfb:∀x,|f x|≤Bf)(hgb:∀x,|g x|≤Bg)
    (hUf:0≤Uf)(hUg:0≤Ug)(hheatf:∀x,|heat v f x|≤Uf)(hheatg:∀x,|heat v g x|≤Ug)(m:State 2):
    |gaussianAverage (C+covariance v) (fun z=>f (z 0)*g (z 1)) m|≤Uf*Ug:=by
  rw [split hC v f g hf hg hBf hBg hfb hgb]
  change |∫z:State 2,heat v f ((m+z) 0)*heat v g ((m+z) 1) ∂multivariateGaussian 0 C|≤_
  have hb(z:State 2):‖heat v f ((m+z) 0)*heat v g ((m+z) 1)‖≤Uf*Ug:=by
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul (hheatf _) (hheatg _) (abs_nonneg _) hUf
  have hn:=norm_integral_le_of_norm_le (μ:=multivariateGaussian (0:State 2) C)
    (f:=fun z:State 2=>heat v f ((m+z) 0)*heat v g ((m+z) 1))
    (integrable_const (Uf*Ug)) (ae_of_all _ hb)
  simpa only [Real.norm_eq_abs,integral_const,probReal_univ,one_smul] using hn

end SHE.GaussianTwoPointReserve
