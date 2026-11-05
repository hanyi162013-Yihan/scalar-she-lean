module

public import SHE.NativeOldSplit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! The old rank-one Gaussian covariance is exactly a scalar Gaussian
root increment with every older unaffected coordinate fixed to zero. -/
namespace SHE.NativeOldLaw
open Set MeasureTheory ProbabilityTheory Real NativeOldSplit GaussianIncrement GaussianAudit
open scoped NNReal InnerProductSpace

def rootEmbed (z:ℝ):State 2:=z•EuclideanSpace.basisFun (Fin 2) ℝ 0

theorem rootCovariance_positive {v:ℝ}(hv:0≤v):(rootCovariance v).PosSemidef:=by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only[star_trivial,rootCovariance,and_comm]
  · intro z
    simp only[dotProduct,Matrix.mulVec,Fin.sum_univ_two,star_trivial,Pi.star_apply,rootCovariance]
    norm_num
    nlinarith[mul_nonneg hv (sq_nonneg (z 0))]

/-- Equality of actual measures, including zero variance. -/
theorem root_gaussian_eq_scalar_map (v:ℝ≥0):
    multivariateGaussian (0:State 2) (rootCovariance v)=(gaussianReal 0 v).map rootEmbed:=by
  let μ:=multivariateGaussian (0:State 2) (rootCovariance v)
  have hA:(rootCovariance (v:ℝ)).PosSemidef:=rootCovariance_positive v.coe_nonneg
  have hv1:Var[EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2);μ]=0:=by
    rw[show Var[EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2);μ]=(rootCovariance v) 1 1 by
      exact variance_eval_multivariateGaussian hA 1]
    norm_num[rootCovariance]
  have hzero:∀ᵐ y:State 2 ∂μ,y 1=0:=by
    have hh:=ae_eq_integral_of_variance_eq_zero
      (IsGaussian.memLp_dual μ (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)) 2 (by norm_num)) hv1
    have hm:(∫y:State 2,y 1 ∂μ)=0:=coordinate_mean (rootCovariance v) 1
    simpa only[EuclideanSpace.coe_proj,hm] using hh
  have hid:(fun y:State 2=>rootEmbed (y 0))=ᵐ[μ] id:=by
    filter_upwards[hzero] with y hy
    apply PiLp.ext
    intro i
    fin_cases i <;> simp[rootEmbed,hy]
  have hmap:μ.map (fun y:State 2=>y 0)=gaussianReal 0 v:=by
    have hh:=(measurePreserving_eval_multivariateGaussian (μ:=(0:State 2)) hA (i:=(0:Fin 2))).map_eq
    simpa [rootCovariance,μ] using hh
  calc
    μ=μ.map id:=(Measure.map_id (μ:=μ)).symm
    _=μ.map (fun y:State 2=>rootEmbed (y 0)):=Measure.map_congr hid.symm
    _=(μ.map (fun y:State 2=>y 0)).map rootEmbed:=by
      rw[Measure.map_map (by unfold rootEmbed;fun_prop) (by fun_prop)]
      rfl
    _=_:=by rw[hmap]

/-- The old scalar factor used in the word is the exact root covariance
law, not merely a Gaussian with matching scaling. -/
theorem root_gaussian_integral (v:ℝ≥0)(F:State 2→ℝ)(hF:Measurable F):
    (∫y,F y ∂multivariateGaussian 0 (rootCovariance v))=∫z,F (rootEmbed z) ∂gaussianReal 0 v:=by
  rw[root_gaussian_eq_scalar_map,integral_map (by unfold rootEmbed;fun_prop) hF.aestronglyMeasurable]

end SHE.NativeOldLaw
