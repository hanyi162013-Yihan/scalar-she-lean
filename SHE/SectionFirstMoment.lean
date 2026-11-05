module

public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.SectionFirstMoment
open MeasureTheory
variable {Ω W : Type*} [MeasurableSpace Ω] [MeasurableSpace W]

/-- An absolute FIRST-moment envelope is integrated before any signed
parameter average. No independence and no square-integrable envelope
are required. -/
theorem joint_integrable (μ : Measure Ω) (ν : Measure W) [SFinite μ] [SFinite ν]
    (F : Ω×W→ℝ) (hF : Measurable F) (B : W→ℝ) (hB : Integrable B ν)
    (hs : ∀ᵐ w ∂ν,Integrable (fun ω=>F (ω,w)) μ ∧
      (∫ ω,|F (ω,w)| ∂μ)≤B w) :
    Integrable F (μ.prod ν) ∧ (∫ z,|F z| ∂μ.prod ν)≤∫ w,B w ∂ν := by
  have hn : ∀ᵐ w ∂ν,(∫ ω,‖F (ω,w)‖ ∂μ)≤B w:=by
    simpa only [Real.norm_eq_abs] using hs.mono (fun _ h=>h.2)
  have hi : Integrable (fun w=>∫ ω,‖F (ω,w)‖ ∂μ) ν:=by
    apply hB.mono' hF.norm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
    filter_upwards [hn] with w hw
    rw [Real.norm_of_nonneg (integral_nonneg (fun _=>norm_nonneg _))]
    exact hw
  have hj : Integrable F (μ.prod ν):=
    (integrable_prod_iff' hF.aestronglyMeasurable).mpr ⟨hs.mono (fun _ h=>h.1),hi⟩
  refine ⟨hj,?_⟩
  change (∫ z,‖F z‖ ∂μ.prod ν)≤_
  rw [integral_prod_symm _ hj.norm]
  exact integral_mono_ae hi hB hn
end SHE.SectionFirstMoment
