module

public import SHE.WeightedSFiniteMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.SignedInputMoments
open Set Filter MeasureTheory ProbabilityTheory Real
variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
variable (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure X) [SFinite ν]

/-- A genuine signed continuum input is averaged using its ACTUAL
positive score energy. The deterministic old-word scale is retained
outside its L1 input mass; no spatial supremum or independent factor
is introduced. Pointwise moment and weighted-input integrability suffice. -/
theorem weighted_even_moment (F : Ω×X→ℝ) (hF : Measurable F)
    (V e : X→ℝ) (hV : Measurable V) (he : Measurable e)
    (hVpos : ∀ᵐ x ∂ν,0≤V x) (hEnergy : Integrable (fun x=>|e x| *V x) ν)
    {K C : ℝ} (hK : 0≤K) (hC : 0≤C) (b : ℕ) (hb : 0<b)
    (hi : ∀ᵐ x ∂ν,Integrable (fun ω=>|F (ω,x)|^(2*b)) μ)
    (hbound : ∀ᵐ x ∂ν,(∫ ω,|F (ω,x)|^(2*b) ∂μ)≤C*(V x*K)^(2*b)) :
    Integrable (fun ω=>|∫ x,e x*F (ω,x) ∂ν|^(2*b)) μ ∧
      (∫ ω,|∫ x,e x*F (ω,x) ∂ν|^(2*b) ∂μ)≤
        C*(K*∫ x,|e x| *V x ∂ν)^(2*b) := by
  let G : Ω×X→ℝ := fun z=>e z.2*F z
  let H : X→ℝ := fun x=>|e x| *|V x| *K
  have hG : Measurable G := (he.comp measurable_snd).mul hF
  have hH : Measurable H := (continuous_abs.measurable.comp he).mul
    (continuous_abs.measurable.comp hV) |>.mul_const K
  have hHi : Integrable H ν := by
    have hh := hEnergy.norm.mul_const K
    simpa only [H,Real.norm_eq_abs,abs_mul,abs_abs] using hh
  have hHpos (x : X) : 0≤H x := mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hK
  have hgi : ∀ᵐ x ∂ν,Integrable (fun ω=>|G (ω,x)|^(2*b)) μ := by
    filter_upwards [hi] with x hx
    simpa only [G,abs_mul,mul_pow] using hx.const_mul (|e x|^(2*b))
  have hgb : ∀ᵐ x ∂ν,(∫ ω,|G (ω,x)|^(2*b) ∂μ)≤C*(H x)^(2*b) := by
    filter_upwards [hbound,hVpos] with x hx hxpos
    simp only [G,abs_mul,mul_pow,integral_const_mul]
    have hh := mul_le_mul_of_nonneg_left hx (pow_nonneg (abs_nonneg (e x)) (2*b))
    simpa only [H,abs_of_nonneg hxpos,mul_pow,mul_assoc,mul_left_comm,mul_comm] using hh
  have hh := WeightedSFiniteMoments.nonnegative_envelope μ ν G hG H hH hHi hHpos b hb C hC hgi hgb
  have hmass : (∫ x,H x ∂ν)=K*∫ x,|e x| *V x ∂ν := by
    have hHval : H=ᵐ[ν] fun x=>(|e x| *V x)*K := by
      filter_upwards [hVpos] with x hx
      simp only [H,abs_of_nonneg hx]
    rw [integral_congr_ae hHval,integral_mul_const,mul_comm]
  exact ⟨hh.1,by simpa only [G,hmass] using hh.2⟩

end SHE.SignedInputMoments
