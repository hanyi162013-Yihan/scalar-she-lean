module

public import SHE.CommonHaarDefectTrace
public import SHE.HaarTraceSpatialRMS

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace SHE.HaarDefectSpatialEnergy
open Set MeasureTheory Real

/-- Root energy of the FULL two-cross-plus-quadratic mark. Either
cross slot may carry the actual signed trace; no correlation is removed
and no positive domination is interpreted as signed smoothing. -/
theorem energy {X:Type*}[MeasurableSpace X](μ:Measure X)
    (F f₁ f₂ f₃ aR aC bR bC:X→ℝ)(hF:Measurable F)
    (hiR:Integrable aR μ)(hiC:Integrable aC μ)
    (hR:∀x,0≤aR x)(hC:∀x,0≤aC x)
    {G BR BC BD:ℝ}(hG:0≤G)(hBR:0≤BR)(hBC:0≤BC)(hBD:0≤BD)
    (hbR:∀x,bR x≤BR)(hbC:∀x,bC x≤BC)(haC:∀x,aC x≤BD)
    (he:∀x,F x=(f₁ x+f₂ x+f₃ x)/2)
    (hp:∀ᵐx∂μ,
      |f₁ x|≤G*(sqrt (aR x)*sqrt (bC x)) ∧
      |f₂ x|≤G*(sqrt (bR x)*sqrt (aC x)) ∧
      |f₃ x|≤G*(sqrt (aR x)*sqrt (aC x)))
    (hbR0:∀x,0≤bR x)(hbC0:∀x,0≤bC x):
    Integrable (fun x=>|F x|^2) μ ∧
      (∫x,|F x|^2 ∂μ)≤(3/4:ℝ)*G^2*((BC+BD)*(∫x,aR x ∂μ)+BR*(∫x,aC x ∂μ)):=by
  let M:=fun x=>(3/4:ℝ)*G^2*((BC+BD)*aR x+BR*aC x)
  have hM:Integrable M μ:=((hiR.const_mul (BC+BD)).add (hiC.const_mul BR)).const_mul _
  have hpw:∀ᵐx∂μ,|F x|^2≤M x:=by
    filter_upwards [hp] with x hx
    have h₁:=pow_le_pow_left₀ (abs_nonneg _) hx.1 2
    have h₂:=pow_le_pow_left₀ (abs_nonneg _) hx.2.1 2
    have h₃:=pow_le_pow_left₀ (abs_nonneg _) hx.2.2 2
    simp only [mul_pow,sq_sqrt (hR x),sq_sqrt (hC x),sq_sqrt (hbR0 x),sq_sqrt (hbC0 x),sq_abs] at h₁ h₂ h₃
    have hc₁:=mul_le_mul_of_nonneg_left (hbC x) (hR x)
    have hc₂:=mul_le_mul_of_nonneg_right (hbR x) (hC x)
    have hc₃:=mul_le_mul_of_nonneg_left (haC x) (hR x)
    have hp₁:=h₁.trans (mul_le_mul_of_nonneg_left hc₁ (sq_nonneg G))
    have hp₂:=h₂.trans (mul_le_mul_of_nonneg_left hc₂ (sq_nonneg G))
    have hp₃:=h₃.trans (mul_le_mul_of_nonneg_left hc₃ (sq_nonneg G))
    have hs:(f₁ x+f₂ x+f₃ x)^2≤3*(f₁ x^2+f₂ x^2+f₃ x^2):=by
      nlinarith [sq_nonneg (f₁ x-f₂ x),sq_nonneg (f₁ x-f₃ x),sq_nonneg (f₂ x-f₃ x)]
    rw [he x,sq_abs]
    dsimp only [M]
    nlinarith
  have hi:Integrable (fun x=>|F x|^2) μ:=
    hM.mono' ((continuous_abs.measurable.comp hF).pow_const 2).aestronglyMeasurable
      (hpw.mono (fun x hx=>by simpa only [Real.norm_eq_abs,abs_pow,abs_abs] using hx))
  refine ⟨hi,(integral_mono_ae hi hM hpw).trans_eq ?_⟩
  rw [integral_const_mul,integral_add (hiR.const_mul _) (hiC.const_mul _),
    integral_const_mul,integral_const_mul]

end SHE.HaarDefectSpatialEnergy
