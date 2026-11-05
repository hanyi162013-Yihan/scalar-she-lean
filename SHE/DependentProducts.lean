module

public import SHE.GaussianAudit
public import SHE.ProfileL2
public import Mathlib.Analysis.MeanInequalities

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! Quantitative products of arbitrarily dependent random factors.
Normalization occurs factor by factor before the arithmetic-geometric
mean bound, so physical variance/input scales multiply exactly. -/
namespace SHE.DependentProducts
open MeasureTheory Real Set
open scoped BigOperators

theorem product_le_mean_power {n:ℕ}(hn:0<n)(a:Fin n→ℝ)(ha:∀i,0≤a i):
    (∏i,a i)≤(∑i,a i^n)/(n:ℝ):=by
  have hnR:0<(n:ℝ):=by exact_mod_cast hn
  have hw:(∑_:Fin n,(1:ℝ)/(n:ℝ))=1:=by
    simp only[Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  have hh:=Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _:Fin n=>(1:ℝ)/(n:ℝ)) (fun i=>a i^n)
    (fun _ _=>by positivity) hw (fun i _=>pow_nonneg (ha i) _)
  have he (i:Fin n):(a i^n)^((1:ℝ)/(n:ℝ))=a i:=by
    rw[←Real.rpow_natCast,←Real.rpow_mul (ha i)]
    rw[show (n:ℝ)*((1:ℝ)/(n:ℝ))=1 by field_simp,Real.rpow_one]
  simp_rw[he] at hh
  convert! hh using 1
  simp_rw[div_eq_mul_inv]
  rw[Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem integrable_abs_product {Ω:Type*}[MeasurableSpace Ω](μ:Measure Ω)
    {n:ℕ}(hn:0<n)(f:Fin n→Ω→ℝ)(_hf:∀i,Measurable (f i))
    (hi:∀i,Integrable (fun ω=>|f i ω|^n) μ):
    Integrable (fun ω=>|∏i,f i ω|) μ:=by
  have hm:Measurable (fun ω=>|∏i,f i ω|):=by fun_prop
  have his:Integrable (fun ω=>(∑i,|f i ω|^n)/(n:ℝ)) μ:=
    (integrable_finsetSum _ (fun i _=>hi i)).div_const _
  apply his.mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro ω
  rw[Real.norm_eq_abs,abs_abs,Finset.abs_prod]
  exact product_le_mean_power hn (fun i=>|f i ω|) (fun _=>abs_nonneg _)

theorem abs_integral_product_bound {Ω:Type*}[MeasurableSpace Ω](μ:Measure Ω)
    {n:ℕ}(hn:0<n)(f:Fin n→Ω→ℝ)(_hf:∀i,Measurable (f i))
    (hi:∀i,Integrable (fun ω=>|f i ω|^n) μ){C:ℝ}
    (hb:∀i,(∫ω,|f i ω|^n ∂μ)≤C):
    |∫ω,∏i,f i ω ∂μ|≤C:=by
  have hnR:0<(n:ℝ):=by exact_mod_cast hn
  have his:Integrable (fun ω=>(∑i,|f i ω|^n)/(n:ℝ)) μ:=
    (integrable_finsetSum _ (fun i _=>hi i)).div_const _
  have hh:=norm_integral_le_of_norm_le (f:=fun ω=>∏i,f i ω) his (ae_of_all _ (fun ω=>by
    rw[Real.norm_eq_abs,Finset.abs_prod]
    exact product_le_mean_power hn (fun i=>|f i ω|) (fun _=>abs_nonneg _)))
  rw[Real.norm_eq_abs,integral_div,integral_finsetSum _ (fun i _=>hi i)] at hh
  have hs:(∑i,∫ω,|f i ω|^n ∂μ)≤(n:ℝ)*C:=by
    convert! Finset.sum_le_sum (s:=Finset.univ) (fun i _=>hb i) using 1
    simp
  exact hh.trans ((div_le_iff₀ hnR).mpr (by simpa only[mul_comm] using hs))

theorem scaled_abs_integral_product_bound {Ω:Type*}[MeasurableSpace Ω](μ:Measure Ω)
    {n:ℕ}(hn:0<n)(f:Fin n→Ω→ℝ)(hf:∀i,Measurable (f i))(r:Fin n→ℝ)(hr:∀i,0<r i)
    (hi:∀i,Integrable (fun ω=>|f i ω/r i|^n) μ){C:ℝ}
    (hb:∀i,(∫ω,|f i ω/r i|^n ∂μ)≤C):
    |∫ω,∏i,f i ω ∂μ|≤C*(∏i,r i):=by
  let g:=fun i ω=>f i ω/r i
  have hg:∀i,Measurable (g i):=fun i=>(hf i).div_const _
  have hh:=abs_integral_product_bound μ hn g hg hi hb
  have he (ω:Ω):(∏i,f i ω)=(∏i,r i)*(∏i,g i ω):=by
    rw[←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    dsimp[g]
    field_simp[(hr i).ne']
  simp_rw[he]
  rw[integral_const_mul,abs_mul,abs_of_pos (Finset.prod_pos (fun i _=>hr i))]
  convert! mul_le_mul_of_nonneg_left hh (Finset.prod_nonneg (fun i _=>(hr i).le)) using 1
  ring

/-- Zero physical scales are allowed. Positive regularization is removed
by continuity, so singular Gaussian directions require no extra case or
conditioning bound. -/
theorem nonnegative_scaled_product_bound {Ω:Type*}[MeasurableSpace Ω](μ:Measure Ω)
    {n:ℕ}(hn:0<n)(f:Fin n→Ω→ℝ)(hf:∀i,Measurable (f i))(r:Fin n→ℝ)(hr:∀i,0≤r i)
    (hi:∀i,Integrable (fun ω=>|f i ω|^n) μ){C:ℝ}(hC:0≤C)
    (hb:∀i,(∫ω,|f i ω|^n ∂μ)≤C*r i^n):
    |∫ω,∏i,f i ω ∂μ|≤C*(∏i,r i):=by
  have hε (ε:ℝ)(hε:0<ε):|∫ω,∏i,f i ω ∂μ|≤C*(∏i,(r i+ε)):=by
    have hp:∀i,0<r i+ε:=fun i=>by linarith[hr i]
    have hi':∀i,Integrable (fun ω=>|f i ω/(r i+ε)|^n) μ:=by
      intro i
      simp only[abs_div,abs_of_pos (hp i),div_pow]
      exact (hi i).div_const _
    apply scaled_abs_integral_product_bound μ hn f hf (fun i=>r i+ε) hp hi' (C:=C)
    intro i
    simp only[abs_div,abs_of_pos (hp i),div_pow,integral_div]
    apply (div_le_iff₀ (pow_pos (hp i) _)).2
    exact (hb i).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (hr i) (by linarith: r i≤r i+ε) n) hC)
  have hc:ContinuousAt (fun ε:ℝ=>C*(∏i,(r i+ε))) 0:=by fun_prop
  have ht:=hc.tendsto.mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
  have hh:=ge_of_tendsto ht (by
    filter_upwards[self_mem_nhdsWithin] with ε hεpos
    exact hε ε hεpos)
  simpa only[add_zero] using hh

theorem product_normTwo_bound {Ω:Type*}[MeasurableSpace Ω](μ:Measure Ω)[IsProbabilityMeasure μ]
    {n:ℕ}(hn:0<n)(f:Fin n→Ω→ℝ)(hf:∀i,Measurable (f i))(r:Fin n→ℝ)(hr:∀i,0≤r i)
    (hi:∀i,Integrable (fun ω=>|f i ω|^(2*n)) μ){C:ℝ}(hC:0≤C)
    (hb:∀i,(∫ω,|f i ω|^(2*n) ∂μ)≤C*r i^(2*n)):
    ProfileL2.normTwo μ (fun ω=>∏i,f i ω)≤sqrt C*(∏i,r i):=by
  let g:=fun i ω=>f i ω^2
  have hg:∀i,Measurable (g i):=fun i=>(hf i).pow_const 2
  have hgi:∀i,Integrable (fun ω=>|g i ω|^n) μ:=by
    intro i
    simpa only[g,abs_pow,←pow_mul] using hi i
  have hgb:∀i,(∫ω,|g i ω|^n ∂μ)≤C*(r i^2)^n:=by
    intro i
    simpa only[g,abs_pow,←pow_mul] using hb i
  have hh:=nonnegative_scaled_product_bound μ hn g hg (fun i=>r i^2) (fun _=>sq_nonneg _) hgi hC hgb
  have hprod (ω:Ω):(∏i,g i ω)=(∏i,f i ω)^2:=by dsimp[g];rw[Finset.prod_pow]
  simp_rw[hprod] at hh
  have hiSq:Integrable (fun ω=>(∏i,f i ω)^2) μ:=by
    have hi':=integrable_abs_product μ hn g hg hgi
    simpa only[hprod,abs_pow,sq_abs] using hi'
  rw[abs_of_nonneg (integral_nonneg (fun ω=>sq_nonneg _)),Finset.prod_pow] at hh
  have hh':ProfileL2.normTwo μ (fun ω=>∏i,f i ω)^2≤(sqrt C*(∏i,r i))^2:=by
    rw[ProfileL2.normTwo_sq,mul_pow,sq_sqrt hC]
    exact hh
  exact (sq_le_sq₀ (ProfileL2.normTwo_nonneg _ _)
    (mul_nonneg (sqrt_nonneg _) (Finset.prod_nonneg (fun i _=>hr i)))).mp hh'

end SHE.DependentProducts
