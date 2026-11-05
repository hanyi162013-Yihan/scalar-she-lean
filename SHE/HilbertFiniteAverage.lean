module

public import SHE.HilbertParameterAverage

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.HilbertParameterAverage
open Set Filter MeasureTheory Real
open scoped ENNReal
variable {Ω P E : Type*} [MeasurableSpace Ω] [MeasurableSpace P]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Old-time Minkowski for an arbitrary finite parameter measure. Its
constant is exactly one; normalizing the old-time cube introduces no
spurious mass power. The zero measure is included. -/
theorem finite_energy (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure P) [IsFiniteMeasure ν] (F : P × Ω → E) (hF : Measurable F)
    (A : P → ℝ) (hAm : Measurable A) (hAi : Integrable A ν) (hA0 : ∀ p,0 ≤ A p)
    (hi : ∀ᵐ p ∂ν,Integrable (fun ω => ‖F (p,ω)‖^2) μ)
    (hb : ∀ᵐ p ∂ν,(∫ ω,‖F (p,ω)‖^2 ∂μ) ≤ A p^2) :
    Integrable F (ν.prod μ) ∧
      Integrable (fun ω => ‖∫ p,F (p,ω) ∂ν‖^2) μ ∧
      (∫ ω,‖∫ p,F (p,ω) ∂ν‖^2 ∂μ) ≤ (∫ p,A p ∂ν)^2 := by
  by_cases hν : ν=0
  · simp [hν]
  have hm0 : ν univ ≠ 0 := Measure.measure_univ_ne_zero.mpr hν
  have hmTop : ν univ ≠ ⊤ := measure_ne_top ν univ
  let d : ENNReal := (ν univ)⁻¹
  have hd0 : d ≠ 0 := ENNReal.inv_ne_zero.mpr hmTop
  have hdTop : d ≠ ⊤ := ENNReal.inv_ne_top.mpr hm0
  let c : ℝ := d.toReal
  have hc : 0 < c := ENNReal.toReal_pos hd0 hdTop
  let η : Measure P := d • ν
  letI : IsProbabilityMeasure η := ⟨by
    change d*ν univ=1
    exact ENNReal.inv_mul_cancel hm0 hmTop⟩
  have hs := energy μ η F hF A hAm (hAi.smul_measure hdTop) hA0
    (Measure.ae_smul_measure hi d) (Measure.ae_smul_measure hb d)
  have he (ω : Ω) : ‖∫ p,F (p,ω) ∂η‖^2=c^2*‖∫ p,F (p,ω) ∂ν‖^2 := by
    rw [show η=d • ν from rfl,integral_smul_measure,norm_smul,
      Real.norm_of_nonneg hc.le,mul_pow]
  have hf : (fun ω => ‖∫ p,F (p,ω) ∂η‖^2)=
      fun ω => c^2*‖∫ p,F (p,ω) ∂ν‖^2 := funext he
  have hscaled : Integrable (fun ω => c^2*‖∫ p,F (p,ω) ∂ν‖^2) μ := by
    simpa only [hf] using hs.2.1
  have ha : Integrable (fun ω => ‖∫ p,F (p,ω) ∂ν‖^2) μ :=
    (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (pow_ne_zero 2 hc.ne')) _).mp hscaled
  refine ⟨joint_integrable μ ν F hF A hAi (ae_of_all _ hA0) hi hb,ha,?_⟩
  have hbound := hs.2.2
  rw [hf,integral_const_mul] at hbound
  have hmass : (∫ p,A p ∂η)=c*(∫ p,A p ∂ν) := by
    rw [show η=d • ν from rfl,integral_smul_measure]
    rfl
  rw [hmass,mul_pow] at hbound
  exact le_of_mul_le_mul_left hbound (sq_pos_of_pos hc)

end SHE.HilbertParameterAverage
