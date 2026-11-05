module

public import SHE.TwoFreshBoundedHaarContraction
public import SHE.ParentHeatFields
public import SHE.WeightedSpatialMoments

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace SHE.HaarTraceSpatialRMS
open Set MeasureTheory Real
open scoped ENNReal

/-- The signed Haar score is integrated only AFTER squaring the actual
complete packet. Thus a spatial trace yields a true output L2 bound,
without replacing it by a scalar root pairing. -/
theorem energy_ae {X:Type*}[MeasurableSpace X](μ:Measure X)
    (F a b:X→ℝ)(hF:Measurable F)(ha:Integrable a μ)(ha0:∀x,0≤a x)
    (hb0:∀x,0≤b x){C B:ℝ}(hC:0≤C)(hB:0≤B)(hb:∀x,b x≤B)
    (hpoint:∀ᵐx∂μ,|F x|≤C*(sqrt (a x)*sqrt (b x))):
    Integrable (fun x=>|F x|^2) μ ∧
      (∫x,|F x|^2 ∂μ)≤C^2*B*(∫x,a x ∂μ):=by
  have hp:∀ᵐx∂μ,|F x|^2≤C^2*B*a x:=by
    filter_upwards [hpoint] with x hx
    have hh:=pow_le_pow_left₀ (abs_nonneg _) hx 2
    rw [mul_pow,mul_pow,sq_sqrt (ha0 x),sq_sqrt (hb0 x)] at hh
    calc
      _≤C^2*(a x*b x):=hh
      _≤C^2*(a x*B):=mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hb x) (ha0 x)) (sq_nonneg _)
      _=C^2*B*a x:=by ring
  have hi:Integrable (fun x=>|F x|^2) μ:=
    (ha.const_mul (C^2*B)).mono' ((continuous_abs.measurable.comp hF).pow_const 2).aestronglyMeasurable
      (hp.mono (fun x hx=>by simpa only [Real.norm_eq_abs,abs_pow,abs_abs] using hx))
  refine ⟨hi,?_⟩
  exact (integral_mono_ae hi (ha.const_mul (C^2*B)) hp).trans_eq (integral_const_mul _ _)

theorem energy {X:Type*}[MeasurableSpace X](μ:Measure X)
    (F a b:X→ℝ)(hF:Measurable F)(ha:Integrable a μ)(ha0:∀x,0≤a x)
    (hb0:∀x,0≤b x){C B:ℝ}(hC:0≤C)(hB:0≤B)(hb:∀x,b x≤B)
    (hpoint:∀x,|F x|≤C*(sqrt (a x)*sqrt (b x))):
    Integrable (fun x=>|F x|^2) μ ∧
      (∫x,|F x|^2 ∂μ)≤C^2*B*(∫x,a x ∂μ):=
  energy_ae μ F a b hF ha ha0 hb0 hC hB hb (ae_of_all _ hpoint)

theorem rms {X:Type*}[MeasurableSpace X](μ:Measure X)
    (F a b:X→ℝ)(hF:Measurable F)(ha:Integrable a μ)(ha0:∀x,0≤a x)
    (hb0:∀x,0≤b x){C B A:ℝ}(hC:0≤C)(hB:0≤B)(hA:0≤A)
    (hb:∀x,b x≤B)(hmass:(∫x,a x ∂μ)≤A)
    (hpoint:∀x,|F x|≤C*(sqrt (a x)*sqrt (b x))):
    Integrable (fun x=>|F x|^2) μ ∧
      sqrt (∫x,|F x|^2 ∂μ)≤C*sqrt B*sqrt A:=by
  obtain ⟨hi,hh⟩:=energy μ F a b hF ha ha0 hb0 hC hB hb hpoint
  refine ⟨hi,?_⟩
  have hp:=hh.trans (mul_le_mul_of_nonneg_left hmass (mul_nonneg (sq_nonneg _) hB))
  have hs:=sqrt_le_sqrt hp
  rw [sqrt_mul (mul_nonneg (sq_nonneg C) hB),sqrt_mul (sq_nonneg C),sqrt_sq hC] at hs
  exact hs

end SHE.HaarTraceSpatialRMS
