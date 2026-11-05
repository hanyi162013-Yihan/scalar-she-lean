module
public import SHE.PositiveKernelSchur
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.PositiveKernelMarginal
open Set MeasureTheory
variable {X:Type*}[MeasurableSpace X](ν:Measure X)[IsFiniteMeasure ν]

/-- The normalized positive heat mass and its true supremum bound give
both alternatives in the clipped Schur mass. -/
theorem clipped (K g:X→ℝ)(hK:Measurable K)(hg:Measurable g){C M:ℝ}
    (hC:0≤C)(hK0:∀x,0≤K x)(hKb:∀x,K x≤C)(hKm:(∫x,K x ∂ν)=1)
    (hg0:∀x,0≤g x)(hgb:∀x,g x≤1)(hgm:(∫x,g x ∂ν)≤M):
    (∫x,K x*g x ∂ν)≤min 1 (C*M):=by
  have hiK:Integrable K ν:=by
    apply (integrable_const C).mono' hK.aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs,abs_of_nonneg (hK0 x)]
    exact hKb x
  have hig:Integrable g ν:=by
    apply (integrable_const (1:ℝ)).mono' hg.aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs,abs_of_nonneg (hg0 x)]
    exact hgb x
  have hi:Integrable (fun x=>K x*g x) ν:=by
    apply (integrable_const C).mono' (hK.mul hg).aestronglyMeasurable
    filter_upwards with x
    change ‖K x*g x‖≤C
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hK0 x) (hg0 x))]
    exact (mul_le_of_le_one_right (hK0 x) (hgb x)).trans (hKb x)
  apply le_min
  · rw [←hKm]
    exact integral_mono hi hiK (fun x=>mul_le_of_le_one_right (hK0 x) (hgb x))
  · calc
      _≤∫x,C*g x ∂ν:=integral_mono hi (hig.const_mul C)
        (fun x=>mul_le_mul_of_nonneg_right (hKb x) (hg0 x))
      _=C*(∫x,g x ∂ν):=integral_const_mul _ _
      _≤C*M:=mul_le_mul_of_nonneg_left hgm hC

end SHE.PositiveKernelMarginal
