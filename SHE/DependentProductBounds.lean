module

public import SHE.DependentProducts

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.DependentProductBounds
open Set MeasureTheory Real DependentProducts ProfileL2
open scoped BigOperators

theorem product_memLp {Ω:Type*}[MeasurableSpace Ω](μ:Measure Ω)
    {n:ℕ}(hn:0<n)(f:Fin n→Ω→ℝ)(hf:∀i,Measurable (f i))
    (hi:∀i,Integrable (fun ω=>|f i ω|^(2*n)) μ):MemLp (fun ω=>∏i,f i ω) 2 μ:=by
  let g:=fun i ω=>f i ω^2
  have hg:∀i,Measurable (g i):=fun i=>(hf i).pow_const 2
  have hgi:∀i,Integrable (fun ω=>|g i ω|^n) μ:=by
    intro i
    simpa only[g,abs_pow,←pow_mul] using hi i
  have hi':=integrable_abs_product μ hn g hg hgi
  have hprod (ω:Ω):(∏i,g i ω)=(∏i,f i ω)^2:=by dsimp[g];rw[Finset.prod_pow]
  have hiSq:Integrable (fun ω=>(∏i,f i ω)^2) μ:=by
    simpa only[hprod,abs_pow,sq_abs] using hi'
  exact (memLp_two_iff_integrable_sq (by fun_prop)).2 hiSq

theorem fintype_product_normTwo {I Ω:Type*}[Fintype I][MeasurableSpace Ω]
    (μ:Measure Ω)[IsProbabilityMeasure μ](hn:0<Fintype.card I)
    (f:I→Ω→ℝ)(hf:∀i,Measurable (f i))(r:I→ℝ)(hr:∀i,0≤r i)
    (hi:∀i,Integrable (fun ω=>|f i ω|^(2*Fintype.card I)) μ){C:ℝ}(hC:0≤C)
    (hb:∀i,(∫ω,|f i ω|^(2*Fintype.card I) ∂μ)≤C*r i^(2*Fintype.card I)):
    normTwo μ (fun ω=>∏i,f i ω)≤sqrt C*(∏i,r i):=by
  classical
  let e:Fin (Fintype.card I)≃I:=(Fintype.equivFin I).symm
  have hh:=product_normTwo_bound μ hn (fun i=>f (e i)) (fun i=>hf (e i))
    (fun i=>r (e i)) (fun i=>hr (e i)) (fun i=>hi (e i)) hC (fun i=>hb (e i))
  have he:(fun ω=>∏i,f (e i) ω)=(fun ω=>∏i,f i ω):=by
    funext ω
    exact e.prod_comp (fun i=>f i ω)
  rw[he,e.prod_comp] at hh
  exact hh

/-- A clipped root or another bounded multiplier may dominate the whole
word pointwise. The true physical factor scales remain multiplicative. -/
theorem dominated_product_normTwo {Ω:Type*}[MeasurableSpace Ω](μ:Measure Ω)[IsProbabilityMeasure μ]
    {n:ℕ}(hn:0<n)(f:Fin n→Ω→ℝ)(hf:∀i,Measurable (f i))(r:Fin n→ℝ)(hr:∀i,0≤r i)
    (hi:∀i,Integrable (fun ω=>|f i ω|^(2*n)) μ){C B:ℝ}(hC:0≤C)(hB:0≤B)
    (hb:∀i,(∫ω,|f i ω|^(2*n) ∂μ)≤C*r i^(2*n))
    (T:Ω→ℝ)(hT:Measurable T)(hdom:∀ω,|T ω|≤B*(∏i,|f i ω|)):
    normTwo μ T≤B*sqrt C*(∏i,r i):=by
  have hp:=product_memLp μ hn f hf hi
  have hTp:MemLp T 2 μ:=(hp.const_mul B).mono hT.aestronglyMeasurable (ae_of_all _ (fun ω=>by
    rw[Real.norm_eq_abs,Real.norm_eq_abs,abs_mul,abs_of_nonneg hB,Finset.abs_prod]
    exact hdom ω))
  have hnorm:=normTwo_mono hTp (hp.const_mul B) (ae_of_all _ (fun ω=>by
    rw[abs_mul,abs_of_nonneg hB,Finset.abs_prod]
    exact hdom ω))
  rw[normTwo_const_mul hp B,abs_of_nonneg hB] at hnorm
  have hh:=product_normTwo_bound μ hn f hf r hr hi hC hb
  convert! hnorm.trans (mul_le_mul_of_nonneg_left hh hB) using 1
  ring

end SHE.DependentProductBounds
