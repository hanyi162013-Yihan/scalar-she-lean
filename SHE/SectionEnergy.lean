module

public import SHE.HilbertTimeAverage

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.SectionEnergy
open MeasureTheory
variable {Ω T E : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
variable [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- A genuine section energy envelope supplies product energy, with the
probability integral taken before current-time integration. -/
theorem product_energy (μ : Measure Ω) [SFinite μ] (τ : Measure T) [SFinite τ]
    (F : T × Ω → E) (hF : Measurable F) (B : T → ℝ) (hBi : Integrable B τ)
    (hi : ∀ᵐ t ∂τ,Integrable (fun ω => ‖F (t,ω)‖^2) μ)
    (hb : ∀ᵐ t ∂τ,(∫ ω,‖F (t,ω)‖^2 ∂μ)≤B t) :
    Integrable (fun z => ‖F z‖^2) (τ.prod μ) ∧
      (∫ z,‖F z‖^2 ∂τ.prod μ)≤∫ t,B t ∂τ := by
  have hm : Measurable (fun t => ∫ ω,‖F (t,ω)‖^2 ∂μ) :=
    (hF.norm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable
  have ht : Integrable (fun t => ∫ ω,‖F (t,ω)‖^2 ∂μ) τ := by
    apply hBi.mono' hm.aestronglyMeasurable
    filter_upwards [hb] with t ht
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
    exact ht
  have hj : Integrable (fun z => ‖F z‖^2) (τ.prod μ) := by
    apply (integrable_prod_iff (hF.norm.pow_const 2).aestronglyMeasurable).mpr
    refine ⟨hi,?_⟩
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using ht
  refine ⟨hj,?_⟩
  rw [integral_prod _ hj]
  exact integral_mono_ae ht hBi hb

end SHE.SectionEnergy
