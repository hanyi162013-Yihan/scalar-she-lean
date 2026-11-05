module

public import SHE.GaussianEnvelopeMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

/-! A rough leaf at a changing current state need not be centered by its
own Gaussian expectation. Its actual baseline discrepancy is retained as
a separate moment, with no independence or Gaussianity of the mean. -/
namespace SHE.RoughLeafOffsetMoments
open Set MeasureTheory ProbabilityTheory Real GaussianAudit GaussianEnvelopeMoments
open scoped NNReal

theorem offset_even_moment {Ω:Type*}[MeasurableSpace Ω](μ:Measure Ω)
    (a:ℝ→ℝ)(ha:Measurable a)(m Y b:Ω→ℝ)(hm:Measurable m)(hY:Measurable Y)(hb:Measurable b)
    {H β:ℝ}(hH:0≤H)(_hβ:0≤β)(hholder:∀z w,|a z-a w|≤H*|z-w|^β)(p:ℕ)
    (hiY:Integrable (fun ω=>|Y ω|^(((2*p:ℕ):ℝ)*β)) μ)
    (hiOffset:Integrable (fun ω=>|a (m ω)-b ω|^(2*p)) μ):
    Integrable (fun ω=>|a (m ω+Y ω)-b ω|^(2*p)) μ ∧
    (∫ω,|a (m ω+Y ω)-b ω|^(2*p) ∂μ)≤
      (2:ℝ)^(2*p-1)*(H^(2*p)*(∫ω,|Y ω|^(((2*p:ℕ):ℝ)*β) ∂μ)+
        (∫ω,|a (m ω)-b ω|^(2*p) ∂μ)):=by
  let R:=fun ω=>(2:ℝ)^(2*p-1)*(H^(2*p)*|Y ω|^(((2*p:ℕ):ℝ)*β)+|a (m ω)-b ω|^(2*p))
  have hRi:Integrable R μ:=((hiY.const_mul _).add hiOffset).const_mul _
  have hpoint (ω:Ω):|a (m ω+Y ω)-b ω|≤H*|Y ω|^β+|a (m ω)-b ω|:=by
    have hh:=hholder (m ω+Y ω) (m ω)
    rw[add_sub_cancel_left] at hh
    have ht:=abs_add_le (a (m ω+Y ω)-a (m ω)) (a (m ω)-b ω)
    have he:a (m ω+Y ω)-a (m ω)+(a (m ω)-b ω)=a (m ω+Y ω)-b ω:=by ring
    rw[he] at ht
    exact ht.trans (add_le_add hh le_rfl)
  have hpow (ω:Ω):|a (m ω+Y ω)-b ω|^(2*p)≤R ω:=by
    have hh:=pow_le_pow_left₀ (abs_nonneg _) (hpoint ω) (2*p)
    have hp:=add_pow_le (mul_nonneg hH (rpow_nonneg (abs_nonneg (Y ω)) β)) (abs_nonneg (a (m ω)-b ω)) (2*p)
    have he:(|Y ω|^β)^(2*p)=|Y ω|^(((2*p:ℕ):ℝ)*β):=by
      rw[←Real.rpow_natCast,←Real.rpow_mul (abs_nonneg _)]
      congr 1;ring
    rw[mul_pow,he] at hp
    exact hh.trans hp
  have hi:Integrable (fun ω=>|a (m ω+Y ω)-b ω|^(2*p)) μ:=by
    have hmf:Measurable (fun ω=>|a (m ω+Y ω)-b ω|^(2*p)):=
      (continuous_abs.measurable.comp ((ha.comp (hm.add hY)).sub hb)).pow_const _
    apply hRi.mono' hmf.aestronglyMeasurable
    exact ae_of_all _ (fun ω=>by
      rw[Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (abs_nonneg _) _)];exact hpow ω)
  refine ⟨hi,(integral_mono hi hRi hpow).trans_eq ?_⟩
  rw[integral_const_mul,integral_add (hiY.const_mul _) hiOffset,integral_const_mul]

/-- The Gaussian noise term is evaluated exactly, while the actual
current-state/profile-baseline discrepancy remains visible. -/
theorem gaussian_offset_even_moment {Ω:Type*}[MeasurableSpace Ω](μ:Measure Ω)
    (a:ℝ→ℝ)(ha:Measurable a)(m Y b:Ω→ℝ)(hm:Measurable m)(hY:Measurable Y)(hb:Measurable b)
    {v:ℝ≥0}(hLaw:HasLaw Y (gaussianReal 0 v) μ){H β:ℝ}(hH:0≤H)(hβ:0≤β)
    (hholder:∀z w,|a z-a w|≤H*|z-w|^β)(p:ℕ)
    (hiOffset:Integrable (fun ω=>|a (m ω)-b ω|^(2*p)) μ):
    Integrable (fun ω=>|a (m ω+Y ω)-b ω|^(2*p)) μ ∧
    (∫ω,|a (m ω+Y ω)-b ω|^(2*p) ∂μ)≤
      (2:ℝ)^(2*p-1)*
        (gaussianAbsMoment (((2*p:ℕ):ℝ)*β)*(H*(v:ℝ)^(β/2))^(2*p)+
          (∫ω,|a (m ω)-b ω|^(2*p) ∂μ)):=by
  let q:=((2*p:ℕ):ℝ)*β
  have hq:0≤q:=by dsimp[q];positivity
  have hiY:Integrable (fun ω=>|Y ω|^q) μ:=by
    convert! hLaw.integrable_comp (integrable_gaussian_abs_rpow v q hq) using 1
  have hmom:(∫ω,|Y ω|^q ∂μ)=(v:ℝ)^(q/2)*gaussianAbsMoment q:=by
    have hh:=hLaw.integral_comp (f:=fun z:ℝ=>|z|^q) (by fun_prop)
    change (∫ω,|Y ω|^q ∂μ)=_ at hh
    rw[hh,gaussian_abs_rpow_moment v q hq]
  have hh:=offset_even_moment μ a ha m Y b hm hY hb hH hβ hholder p hiY hiOffset
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  rw[hmom]
  have he:(v:ℝ)^(q/2)=((v:ℝ)^(β/2))^(2*p):=by
    rw[←Real.rpow_natCast,←Real.rpow_mul v.coe_nonneg]
    congr 1;dsimp[q];ring
  rw[he,mul_pow]
  ring

end SHE.RoughLeafOffsetMoments
