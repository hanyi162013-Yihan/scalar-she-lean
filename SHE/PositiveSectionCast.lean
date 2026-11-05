module
public import Mathlib.MeasureTheory.Integral.Prod
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.PositiveSectionCast
open MeasureTheory
open scoped ENNReal
variable {X Y:Type*} [MeasurableSpace X] [MeasurableSpace Y]
/-- Positive iterated mass can be cast after reversing the two actual
parameter integrals. Section and outer Bochner integrability are explicit. -/
theorem swap (ν:Measure X) (μ:Measure Y) [SFinite ν] [SFinite μ]
    (f:X×Y→ℝ) (hf:Measurable f)
    (hi:∀ᵐx∂ν,Integrable (fun y=>f (x,y)) μ)
    (ho:Integrable (fun x=>∫y,f (x,y) ∂μ) ν)
    (hn:∀ᵐx∂ν,∀ᵐy∂μ,0≤f (x,y)):
    (∫⁻y,∫⁻x,ENNReal.ofReal (f (x,y)) ∂ν ∂μ)=
      ENNReal.ofReal (∫x,∫y,f (x,y) ∂μ ∂ν):=by
  have hm:Measurable (fun p:X×Y=>ENNReal.ofReal (f p)):=ENNReal.measurable_ofReal.comp hf
  calc
    _=(∫⁻x,∫⁻y,ENNReal.ofReal (f (x,y)) ∂μ ∂ν):=(lintegral_lintegral_swap hm.aemeasurable).symm
    _=(∫⁻x,ENNReal.ofReal (∫y,f (x,y) ∂μ) ∂ν):=by
      apply lintegral_congr_ae
      filter_upwards [hi,hn] with x hx hnx
      exact (ofReal_integral_eq_lintegral_ofReal hx hnx).symm
    _=_:=(ofReal_integral_eq_lintegral_ofReal ho (by
      filter_upwards [hn] with x hx
      exact integral_nonneg_of_ae hx)).symm
end SHE.PositiveSectionCast
