module
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.PositiveKernelSchur
open Set MeasureTheory
variable {X:Type*}[MeasurableSpace X](ν:Measure X)[IsFiniteMeasure ν]

/-- Genuine positive-kernel Schur bound on the original spatial
measure. Both marginal masses are used; amplitudes may vary in space. -/
theorem bounded (K:X×X→ℝ)(hK:Measurable K){B C A0:ℝ}
    (hB:0≤B)(hC:0≤C)(hA0:0≤A0)(hK0:∀z,0≤K z)(hKb:∀z,K z≤B)
    (hrow:∀x,(∫y,K (x,y) ∂ν)≤C)(hcol:∀y,(∫x,K (x,y) ∂ν)≤C)
    (A:X→ℝ)(hA:Measurable A)(hAb:∀x,|A x|≤A0):
    (∫x,∫y,K (x,y)*A x*A y ∂ν ∂ν)≤C*(∫x,A x^2 ∂ν):=by
  have hsq(x:X):A x^2≤A0^2:=by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (A x)) (hAb x) 2
  have hkn(z:X×X):|K z|≤B:=by rw [abs_of_nonneg (hK0 z)];exact hKb z
  have hAA(z:X×X):|A z.1*A z.2|≤A0^2:=by
    rw [abs_mul,pow_two]
    exact mul_le_mul (hAb z.1) (hAb z.2) (abs_nonneg _) hA0
  have hi:Integrable (fun z:X×X=>K z*A z.1*A z.2) (ν.prod ν):=by
    apply (integrable_const (B*A0^2)).mono'
      ((hK.mul (hA.comp measurable_fst)).mul (hA.comp measurable_snd)).aestronglyMeasurable
    filter_upwards with z
    change ‖K z*A z.1*A z.2‖≤B*A0^2
    rw [Real.norm_eq_abs,show K z*A z.1*A z.2=K z*(A z.1*A z.2) by ring,abs_mul]
    exact mul_le_mul (hkn z) (hAA z) (abs_nonneg _) hB
  have hiL:Integrable (fun z:X×X=>K z*A z.1^2) (ν.prod ν):=by
    apply (integrable_const (B*A0^2)).mono' (hK.mul ((hA.comp measurable_fst).pow_const 2)).aestronglyMeasurable
    filter_upwards with z
    change ‖K z*A z.1^2‖≤B*A0^2
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hK0 z) (sq_nonneg _))]
    exact mul_le_mul (hKb z) (hsq z.1) (sq_nonneg _) hB
  have hiR:Integrable (fun z:X×X=>K z*A z.2^2) (ν.prod ν):=by
    apply (integrable_const (B*A0^2)).mono' (hK.mul ((hA.comp measurable_snd).pow_const 2)).aestronglyMeasurable
    filter_upwards with z
    change ‖K z*A z.2^2‖≤B*A0^2
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hK0 z) (sq_nonneg _))]
    exact mul_le_mul (hKb z) (hsq z.2) (sq_nonneg _) hB
  have hiA:Integrable (fun x=>A x^2) ν:=by
    apply (integrable_const (A0^2)).mono' (hA.pow_const 2).aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact hsq x
  have hleft:(∫z:X×X,K z*A z.1^2 ∂ν.prod ν)≤C*(∫x,A x^2 ∂ν):=by
    rw [integral_prod _ hiL,←integral_const_mul]
    apply integral_mono_ae hiL.integral_prod_left (hiA.const_mul C)
    filter_upwards with x
    rw [integral_mul_const]
    exact (mul_le_mul_of_nonneg_right (hrow x) (sq_nonneg _))
  have hright:(∫z:X×X,K z*A z.2^2 ∂ν.prod ν)≤C*(∫x,A x^2 ∂ν):=by
    rw [integral_prod_symm _ hiR,←integral_const_mul]
    apply integral_mono_ae hiR.integral_prod_right (hiA.const_mul C)
    filter_upwards with y
    rw [integral_mul_const]
    exact (mul_le_mul_of_nonneg_right (hcol y) (sq_nonneg _))
  rw [←integral_prod _ hi]
  have hb:(∫z:X×X,K z*A z.1*A z.2 ∂ν.prod ν)≤
      (∫z:X×X,(K z*A z.1^2+K z*A z.2^2)/2 ∂ν.prod ν):=by
    apply integral_mono_ae hi ((hiL.add hiR).div_const 2)
    filter_upwards with z
    change K z*A z.1*A z.2≤(K z*A z.1^2+K z*A z.2^2)/2
    nlinarith [mul_nonneg (hK0 z) (sq_nonneg (A z.1-A z.2))]
  simp_rw [div_eq_mul_inv] at hb
  rw [integral_mul_const,integral_add hiL hiR] at hb
  linarith

end SHE.PositiveKernelSchur
