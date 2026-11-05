module
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.BoundedSpatialCovariance
open MeasureTheory
variable {Ω X:Type*}[MeasurableSpace Ω][MeasurableSpace X]

def value (μ:Measure Ω)(F:Ω×X→ℝ)(z:X×X):ℝ:=∫ω,F (ω,z.1)*F (ω,z.2) ∂μ

theorem measurable (μ:Measure Ω)[SFinite μ](F:Ω×X→ℝ)(hF:Measurable F):
    Measurable (value μ F):=by
  have hm:Measurable (fun p:(X×X)×Ω=>F (p.2,p.1.1)*F (p.2,p.1.2)):=
    (hF.comp (measurable_snd.prodMk measurable_fst.fst)).mul
      (hF.comp (measurable_snd.prodMk measurable_fst.snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem norm_bound (μ:Measure Ω)[IsProbabilityMeasure μ](F:Ω×X→ℝ){B:ℝ}
    (hB:0≤B)(hb:∀p,|F p|≤B)(z:X×X):‖value μ F z‖≤B^2:=by
  have h:∀ᵐω∂μ,‖F (ω,z.1)*F (ω,z.2)‖≤B^2:=by
    filter_upwards with ω
    rw [Real.norm_eq_abs,abs_mul,pow_two]
    exact mul_le_mul (hb (ω,z.1)) (hb (ω,z.2)) (abs_nonneg _) hB
  simpa only [Measure.real,measure_univ,ENNReal.toReal_one,one_mul,mul_one,value] using
    (norm_integral_le_of_norm_le_const h)

theorem integrable {Y:Type*}[MeasurableSpace Y](ν:Measure Y)[IsFiniteMeasure ν]
    (f:Y→ℝ)(hf:Measurable f)(C:ℝ)(hb:∀y,‖f y‖≤C):Integrable f ν:=
  (integrable_const C).mono' hf.aestronglyMeasurable (ae_of_all _ hb)

end SHE.BoundedSpatialCovariance
