module
public import SHE.WeightedAverageProduct
public import SHE.SmoothCylinders
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SHE.WeightedAverageDifferentiable
open Set Filter MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution
  SmoothCylinders
variable {X:Type*} [MeasurableSpace X] {n:ℕ}
variable (μ:Measure X)(w:X→ℝ)(hw:Integrable w μ)(hwm:Measurable w)
variable (shift:X→State n)(hs:Measurable shift)
include hw hwm hs

/-- Integrable signed old scores preserve actual differentiability of
bounded smooth tests, without requiring a finite old measure. -/
theorem hasFDerivAt (F:State n→ℝ)(hF:BoundedSmooth F)(z:State n):
    HasFDerivAt (WeightedBorelAverage.average μ w shift F)
      (∫x,w x • fderiv ℝ F (z+shift x) ∂μ) z:=by
  obtain ⟨M,hM⟩:=hF.norm_bound
  obtain ⟨L,hL⟩:=hF.fderiv.norm_bound
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s:=univ)
    (F:=fun z x=>w x*F (z+shift x))
    (F':=fun z x=>w x • fderiv ℝ F (z+shift x))
    (bound:=fun x=>‖w x‖*L) (by simp)
  · exact Eventually.of_forall (fun z=>(hwm.mul
      (hF.smooth.continuous.measurable.comp (measurable_const.add hs))).aestronglyMeasurable)
  · exact WeightedBorelAverage.integrable μ w hw shift hs F hF.smooth.continuous.measurable M
      (fun z=>by simpa only [Real.norm_eq_abs] using hM z) z
  · exact (hwm.smul (hF.fderiv.smooth.continuous.measurable.comp
      (measurable_const.add hs))).aestronglyMeasurable
  · exact Eventually.of_forall (fun x z _=>by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hL _) (norm_nonneg _))
  · exact hw.norm.mul_const L
  · exact Eventually.of_forall (fun x z _=>by
      have he:(fun z=>w x*F (z+shift x))=w x • (fun z=>F (z+shift x)):=by
        funext y
        rfl
      rw [he]
      simpa only [Function.comp_def,id_eq,ContinuousLinearMap.comp_id,Pi.smul_apply,smul_eq_mul] using
        (((hF.smooth.differentiable (by simp) (z+shift x)).hasFDerivAt.comp z
          ((hasFDerivAt_id z).add_const (shift x))).const_smul (w x)))

theorem differentiable (F:State n→ℝ)(hF:BoundedSmooth F):
    Differentiable ℝ (WeightedBorelAverage.average μ w shift F):=
  fun z=>(hasFDerivAt μ w hw hwm shift hs F hF z).differentiableAt

variable [SFinite μ]

/-- The ORIGINAL whole Gaussian word, with signed old weights still
inside, is differentiable. Singular fresh covariances are permitted. -/
theorem gaussian_differentiable (C:MeasurableGeneralizedInverse.Mat n)
    (F:State n→ℝ)(hF:BoundedSmooth F):
    Differentiable ℝ (gaussianAverage C (WeightedBorelAverage.average μ w shift F)):=by
  obtain ⟨M,hM⟩:=hF.norm_bound
  have he:gaussianAverage C (WeightedBorelAverage.average μ w shift F)=
      WeightedBorelAverage.average μ w shift (gaussianAverage C F):=by
    funext z
    simpa only [WeightedBorelAverage.average,gaussianAverage,one_mul,id_eq] using
      WeightedAverageProduct.commute (multivariateGaussian 0 C) μ (fun _=>1) w
        (integrable_const 1) hw id shift measurable_id hs F hF.smooth.continuous.measurable M
        (fun z=>by simpa only [Real.norm_eq_abs] using hM z) z
  rw [he]
  exact differentiable μ w hw hwm shift hs _ (hF.average (multivariateGaussian 0 C))
end SHE.WeightedAverageDifferentiable
