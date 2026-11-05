module

public import SHE.ProfileL2
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.ScalarFibreRMS
open Set MeasureTheory Real ProfileL2
variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
variable (μ : Measure Ω) [SFinite μ] (ν : Measure X) [SFinite ν]

def rms (F : Ω×X→ℝ) (x : X) : ℝ:=sqrt (∫ ω,|F (ω,x)|^2 ∂μ)

theorem nonneg (F : Ω×X→ℝ) (x : X) : 0≤rms μ F x:=sqrt_nonneg _

theorem measurable (F : Ω×X→ℝ) (hF : Measurable F) : Measurable (rms μ F) :=
  ((continuous_abs.measurable.comp hF).pow_const (2:ℕ)).stronglyMeasurable.integral_prod_left'.measurable.sqrt

theorem sq (F : Ω×X→ℝ) (x : X) : (rms μ F x)^2=∫ ω,|F (ω,x)|^2 ∂μ :=
  sq_sqrt (integral_nonneg (fun _=>sq_nonneg _))

/-- Genuine sample/spatial L² energy gives a measurable L² RMS field,
with EXACT energy and no uniform pointwise bound on the random input. -/
theorem memLp_energy (F : Ω×X→ℝ) (hF : Measurable F)
    (hi : Integrable (fun z=>|F z|^2) (μ.prod ν)) :
    MemLp (rms μ F) 2 ν ∧ (normTwo ν (rms μ F))^2=∫ z,|F z|^2 ∂μ.prod ν := by
  have he : (fun x=>(rms μ F x)^2)=(fun x=>∫ ω,|F (ω,x)|^2 ∂μ):=funext (sq μ F)
  have hsq : Integrable (fun x=>(rms μ F x)^2) ν:=by
    rw [he]
    exact hi.integral_prod_right
  refine ⟨(memLp_two_iff_integrable_sq (measurable μ F hF).aestronglyMeasurable).mpr hsq,?_⟩
  rw [normTwo_sq,he]
  exact (integral_prod_symm _ hi).symm

end SHE.ScalarFibreRMS
