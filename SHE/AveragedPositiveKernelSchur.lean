module
public import SHE.PositiveKernelSchur
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.AveragedPositiveKernelSchur
open Set MeasureTheory
variable {Ω X:Type*}[MeasurableSpace Ω][MeasurableSpace X]
variable (μ:Measure Ω)[IsFiniteMeasure μ](ν:Measure X)[IsFiniteMeasure ν]

/-- Schur applied before integrating the random spatial amplitudes.
The two actual sample-dependent displacement factors are retained. -/
theorem bound (Q:X×X→ℝ)(hQ:Measurable Q){B C A0:ℝ}
    (hB:0≤B)(hC:0≤C)(hA0:0≤A0)(hQ0:∀z,0≤Q z)(hQb:∀z,Q z≤B)
    (hr:∀x,(∫y,Q (x,y) ∂ν)≤C)(hc:∀y,(∫x,Q (x,y) ∂ν)≤C)
    (A:Ω×X→ℝ)(hA:Measurable A)(hAb:∀p,|A p|≤A0):
    (∫z:X×X,Q z*(∫ω,A (ω,z.1)*A (ω,z.2) ∂μ) ∂ν.prod ν)≤
      C*(∫ω,∫x,A (ω,x)^2 ∂ν ∂μ):=by
  let R:Ω×(X×X)→ℝ:=fun p=>Q p.2*A (p.1,p.2.1)*A (p.1,p.2.2)
  have hm:Measurable R:=
    ((hQ.comp measurable_snd).mul (hA.comp (measurable_fst.prodMk measurable_snd.fst))).mul
      (hA.comp (measurable_fst.prodMk measurable_snd.snd))
  have hi:Integrable R (μ.prod (ν.prod ν)):=by
    apply (integrable_const (B*A0^2)).mono' hm.aestronglyMeasurable
    filter_upwards with p
    change ‖Q p.2*A (p.1,p.2.1)*A (p.1,p.2.2)‖≤B*A0^2
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_nonneg (hQ0 p.2)]
    have hh:=mul_le_mul (hAb (p.1,p.2.1)) (hAb (p.1,p.2.2)) (abs_nonneg _) hA0
    calc
      _=Q p.2*(|A (p.1,p.2.1)| * |A (p.1,p.2.2)|):=by ring
      _≤B*(A0*A0):=mul_le_mul (hQb p.2) hh (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hB
      _=_:=by ring
  have hiA:Integrable (fun p:Ω×X=>A p^2) (μ.prod ν):=by
    apply (integrable_const (A0^2)).mono' (hA.pow_const 2).aestronglyMeasurable
    filter_upwards with p
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (A p)) (hAb p) 2
  calc
    _=∫z:X×X,∫ω,R (ω,z) ∂μ ∂ν.prod ν:=by
      apply integral_congr_ae
      filter_upwards with z
      dsimp [R]
      simp_rw [mul_assoc]
      rw [integral_const_mul]
    _=∫ω,∫z:X×X,R (ω,z) ∂ν.prod ν ∂μ:=(integral_integral_swap hi).symm
    _≤_:=by
      rw [←integral_const_mul]
      apply integral_mono_ae hi.integral_prod_left (hiA.integral_prod_left.const_mul C)
      filter_upwards [hi.prod_right_ae] with ω hω
      rw [integral_prod _ hω]
      exact PositiveKernelSchur.bounded ν Q hQ hB hC hA0 hQ0 hQb hr hc
        (fun x=>A (ω,x)) (hA.comp (measurable_const.prodMk measurable_id))
        (fun x=>hAb (ω,x))

end SHE.AveragedPositiveKernelSchur
