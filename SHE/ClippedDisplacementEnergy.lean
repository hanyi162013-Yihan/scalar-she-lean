module
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.ClippedDisplacementEnergy
open MeasureTheory Real
variable {X:Type*}[MeasurableSpace X](ν:Measure X)[IsProbabilityMeasure ν]

/-- Clipped random displacement retains its actual second moment. -/
theorem bound (D:X→ℝ)(hD:Measurable D)(hi:Integrable (fun x=>D x^2) ν)
    {r C:ℝ}(hr:0<r)(hC:0≤C):
    Integrable (fun x=>(C*min 1 (|D x|/r))^2) ν ∧
    (∫x,(C*min 1 (|D x|/r))^2 ∂ν)≤C^2*min 1 ((∫x,D x^2 ∂ν)/r^2):=by
  let A:=fun x=>min 1 (|D x|/r)
  have hm:Measurable A:=measurable_const.min ((continuous_abs.measurable.comp hD).div_const r)
  have h0(x):0≤A x:=le_min zero_le_one (div_nonneg (abs_nonneg _) hr.le)
  have h1(x):A x≤1:=min_le_left _ _
  have ha:Integrable (fun x=>A x^2) ν:=by
    apply (integrable_const (1:ℝ)).mono' (hm.pow_const 2).aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact (pow_le_pow_left₀ (h0 x) (h1 x) 2).trans_eq (by norm_num)
  have hsmall:(∫x,A x^2 ∂ν)≤1:=by
    calc
      _≤∫x,(1:ℝ) ∂ν:=by
        apply integral_mono_ae ha (integrable_const _)
        filter_upwards with x
        exact (pow_le_pow_left₀ (h0 x) (h1 x) 2).trans_eq (by norm_num)
      _=1:=by simp
  have hlarge:(∫x,A x^2 ∂ν)≤(∫x,D x^2 ∂ν)/r^2:=by
    rw [←integral_div]
    apply integral_mono_ae ha (hi.div_const _)
    filter_upwards with x
    calc
      _≤(|D x|/r)^2:=pow_le_pow_left₀ (h0 x) (min_le_right _ _) 2
      _=D x^2/r^2:=by rw [div_pow,sq_abs]
  have he:(fun x=>(C*A x)^2)=(fun x=>C^2*A x^2):=by funext x;ring
  rw [he]
  refine ⟨ha.const_mul _,?_⟩
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (le_min hsmall hlarge) (sq_nonneg C)
end SHE.ClippedDisplacementEnergy
