module

public import SHE.GaussianEnvelopeMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.GaussianCenteredLeafMoments
open Set MeasureTheory ProbabilityTheory Real GaussianAudit GaussianEnvelopeMoments ProfileL2
open scoped NNReal

def leafMomentConstant (p:ℕ)(β:ℝ):ℝ:=
  (2:ℝ)^(2*p-1)*(gaussianAbsMoment (((2*p:ℕ):ℝ)*β)+(gaussianAbsMoment β)^(2*p))

theorem leafMomentConstant_nonneg (p:ℕ)(β:ℝ):0≤leafMomentConstant p β:=by
  unfold leafMomentConstant
  positivity[gaussianAbsMoment_nonneg (((2*p:ℕ):ℝ)*β),gaussianAbsMoment_nonneg β]

theorem centered_holder_even_moment {Ω:Type*}[MeasurableSpace Ω](μ:Measure Ω)[IsProbabilityMeasure μ]
    (X:Ω→ℝ)(hXm:Measurable X){v:ℝ≥0}(hX:HasLaw X (gaussianReal 0 v) μ)
    (a:ℝ→ℝ)(ha:Measurable a)(M H β:ℝ)(hM:∀z,|a z|≤M)(hH:0≤H)(hβ:0≤β)
    (hholder:∀z w,|a z-a w|≤H*|z-w|^β)(m:ℝ)(p:ℕ):
    let F:=fun ω=>a (m+X ω)-(∫z,a (m+X z) ∂μ)
    Integrable (fun ω=>|F ω|^(2*p)) μ ∧
      (∫ω,|F ω|^(2*p) ∂μ)≤leafMomentConstant p β*(H*(v:ℝ)^(β/2))^(2*p):=by
  intro F
  let V:=(v:ℝ)^(β/2)
  let g:=gaussianAbsMoment β
  let q:=((2*p:ℕ):ℝ)*β
  have hq:0≤q:=by dsimp[q];positivity
  have hiX:Integrable (fun ω=>|X ω|^β) μ:=by
    convert! hX.integrable_comp (integrable_gaussian_abs_rpow v β hβ) using 1
  have hiQ:Integrable (fun ω=>|X ω|^q) μ:=by
    convert! hX.integrable_comp (integrable_gaussian_abs_rpow v q hq) using 1
  have hXmβ:(∫ω,|X ω|^β ∂μ)=V*g:=by
    have hh:=hX.integral_comp (f:=fun z:ℝ=>|z|^β) (by fun_prop)
    change (∫ω,|X ω|^β ∂μ)=_ at hh
    rw[hh,gaussian_abs_rpow_moment v β hβ]
  have hXmQ:(∫ω,|X ω|^q ∂μ)=(v:ℝ)^(q/2)*gaussianAbsMoment q:=by
    have hh:=hX.integral_comp (f:=fun z:ℝ=>|z|^q) (by fun_prop)
    change (∫ω,|X ω|^q ∂μ)=_ at hh
    rw[hh,gaussian_abs_rpow_moment v q hq]
  have hia:Integrable (fun ω=>a (m+X ω)) μ:=
    (bounded_memLp (ha.comp (measurable_const.add hXm)) (fun ω=>hM _)).integrable (by norm_num)
  have hbaseline:|(∫ω,a (m+X ω) ∂μ)-a m|≤H*V*g:=by
    have hh:=norm_integral_le_of_norm_le (f:=fun ω=>a (m+X ω)-a m) (hiX.const_mul H)
      (ae_of_all _ (fun ω=>by simpa only[Real.norm_eq_abs,add_sub_cancel_left] using hholder (m+X ω) m))
    rw[integral_sub hia (integrable_const _),integral_const,probReal_univ,one_smul,
      integral_const_mul,hXmβ,Real.norm_eq_abs] at hh
    convert! hh using 1
    ring
  have hpoint (ω:Ω):|F ω|≤H*(|X ω|^β+V*g):=by
    have h1:=hholder (m+X ω) m
    rw[add_sub_cancel_left] at h1
    have h2:=abs_add_le (a (m+X ω)-a m) (a m-(∫z,a (m+X z) ∂μ))
    rw[abs_sub_comm (a m)] at h2
    have he:a (m+X ω)-a m+(a m-(∫z,a (m+X z) ∂μ))=F ω:=by dsimp[F];ring
    rw[he] at h2
    exact h2.trans ((add_le_add h1 hbaseline).trans_eq (by ring))
  let R:=fun ω=>((2:ℝ)^(2*p-1)*H^(2*p))*(|X ω|^q+(V*g)^(2*p))
  have hRi:Integrable R μ:=by
    exact (hiQ.add (integrable_const _)).const_mul _
  have hpow (ω:Ω):|F ω|^(2*p)≤R ω:=by
    have hh:=pow_le_pow_left₀ (abs_nonneg (F ω)) (hpoint ω) (2*p)
    rw[mul_pow] at hh
    have hp:=add_pow_le (rpow_nonneg (abs_nonneg (X ω)) β)
      (mul_nonneg (rpow_nonneg v.coe_nonneg (β/2)) (gaussianAbsMoment_nonneg β)) (2*p)
    have he:(|X ω|^β)^(2*p)=|X ω|^q:=by
      rw[←Real.rpow_natCast,←Real.rpow_mul (abs_nonneg _)]
      congr 1;dsimp[q];ring
    rw[he] at hp
    exact hh.trans (by convert! mul_le_mul_of_nonneg_left hp (pow_nonneg hH (2*p)) using 1;ring)
  have hi:Integrable (fun ω=>|F ω|^(2*p)) μ:=by
    have hmF:Measurable F:=(ha.comp (measurable_const.add hXm)).sub_const _
    have hmPow:Measurable (fun ω=>|F ω|^(2*p)):=
      (continuous_abs.measurable.comp hmF).pow_const _
    apply hRi.mono' hmPow.aestronglyMeasurable
    exact ae_of_all _ (fun ω=>by rw[Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (abs_nonneg _) _)];exact hpow ω)
  refine ⟨hi,?_⟩
  have hvpow:(v:ℝ)^(q/2)=V^(2*p):=by
    dsimp[V]
    rw[←Real.rpow_natCast,←Real.rpow_mul v.coe_nonneg]
    congr 1;dsimp[q];ring
  calc
    _≤∫ω,R ω ∂μ:=integral_mono hi hRi hpow
    _=_:=by
      rw[integral_const_mul,integral_add hiQ (integrable_const _),hXmQ,integral_const,probReal_univ,one_smul,hvpow]
      dsimp[leafMomentConstant,g]
      rw[mul_pow,mul_pow]
      ring

end SHE.GaussianCenteredLeafMoments
