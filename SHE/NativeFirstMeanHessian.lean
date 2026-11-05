module

public import SHE.GaussianFullResidualScore
public import SHE.GaussianFixedFirstAverage
public import SHE.ProfileReserveTotalMark

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeFirstMeanHessian
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution
  GaussianRangeSmooth SmoothCylinders MeasurableGaussianScores
variable {n:ℕ}

/-- A native first-score mean mark is the literal mixed Hessian of
the ORIGINAL whole kernel. This lets the genuine original theta-family
Hessian Borel field supply measurability, with no moving-law surrogate. -/
theorem hessian_eq_meanScore {C:MeasurableGeneralizedInverse.Mat n} (hC:C.PosSemidef)
    {E V:State n} (hV:V∈(Matrix.toEuclideanCLM (𝕜:=ℝ) C).range)
    (Original inner:State n→ℝ) (hOriginal:BoundedSmooth Original) (hinner:Measurable inner)
    (M:ℝ) (hbound:∀z,|inner z|≤M)
    (hrep:∀z,fderiv ℝ Original z E=gaussianAverage C inner z) (z:State n):
    GaussianTaylor.hessian Original z V E=
      ∫y,inner (z+y)*firstScore C V y ∂multivariateGaussian (0:State n) C := by
  have hs:=GaussianMeanScores.hasDerivAt_physical_mean hC hV
    (fun y=>inner (z+y)) (hinner.comp (measurable_const.add measurable_id)) M (fun y=>hbound _) 0
  have he:(fun s:ℝ=>∫y,inner (z+(y+s•V)) ∂multivariateGaussian (0:State n) C)=
      (fun s:ℝ=>fderiv ℝ Original (z+s•V) E):=by
    funext s
    rw [hrep]
    apply integral_congr_ae
    exact ae_of_all _ (fun y=>by congr 1;abel)
  rw [he] at hs
  have hline:HasDerivAt (fun s:ℝ=>z+s•V) V 0:=by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const V).const_add z using 1 <;> simp
  have hgrad:=((hOriginal.fderiv.smooth.differentiable (by simp) (z+(0:ℝ)•V)).hasFDerivAt.comp_hasDerivAt 0 hline)
  have hval:=hgrad.clm_apply (hasDerivAt_const (0:ℝ) E)
  simpa only [GaussianTaylor.hessian,zero_smul,add_zero,Function.comp_def,
    map_zero,zero_add] using hval.unique hs

end SHE.NativeFirstMeanHessian
