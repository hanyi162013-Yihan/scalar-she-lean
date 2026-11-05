module

public import SHE.GaussianClipMoments
public import SHE.DependentProductBounds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.GaussianClipProducts
open Set MeasureTheory ProbabilityTheory Real GaussianAudit GaussianClipMoments DependentProducts
open scoped NNReal BigOperators

theorem product_even_moment {Ω:Type*}[MeasurableSpace Ω](μ:Measure Ω)[IsProbabilityMeasure μ]
    {n:ℕ}(hn:0<n)(X:Fin n→Ω→ℝ)(hXm:∀i,Measurable (X i))(v:Fin n→ℝ≥0)
    (hX:∀i,HasLaw (X i) (gaussianReal 0 (v i)) μ){ν:ℝ}(hν:0≤ν)(p:ℕ):
    Integrable (fun ω=>|∏i,clip ν (X i ω)|^(2*p)) μ ∧
      (∫ω,|∏i,clip ν (X i ω)|^(2*p) ∂μ)≤
        clipMomentConstant (p*n)*(∏i,min 1 (ν*sqrt (v i:ℝ)))^(2*p):=by
  let f:=fun i ω=>clip ν (X i ω)^(2*p)
  let r:=fun i=>min 1 (ν*sqrt (v i:ℝ))^(2*p)
  have hf:∀i,Measurable (f i):=fun i=>
    (measurable_const.min (measurable_const.mul (continuous_abs.measurable.comp (hXm i)))).pow_const _
  have hr:∀i,0≤r i:=fun i=>pow_nonneg (le_min (by norm_num) (mul_nonneg hν (sqrt_nonneg _))) _
  have he (i:Fin n)(ω:Ω):|f i ω|^n=|clip ν (X i ω)|^(2*(p*n)):=by
    dsimp[f]
    rw[abs_pow,←pow_mul]
    congr 1
    ring
  have hi:∀i,Integrable (fun ω=>|f i ω|^n) μ:=by
    intro i
    simp_rw[he]
    exact (clip_even_moment μ (X i) (hXm i) (hX i) hν (p*n)).1
  have hb:∀i,(∫ω,|f i ω|^n ∂μ)≤clipMomentConstant (p*n)*r i^n:=by
    intro i
    simp_rw[he]
    convert! (clip_even_moment μ (X i) (hXm i) (hX i) hν (p*n)).2 using 1
    dsimp[r]
    rw[←pow_mul]
    congr 2
    ring
  have hh:=nonnegative_scaled_product_bound μ hn f hf r hr hi (clipMomentConstant_nonneg (p*n)) hb
  have heprod (ω:Ω):|∏i,clip ν (X i ω)|^(2*p)=(∏i,f i ω):=by
    rw[Finset.abs_prod]
    simp_rw[abs_of_nonneg (clip_nonneg hν _)]
    rw[Finset.prod_pow]
  have hprodI:Integrable (fun ω=>∏i,f i ω) μ:=by
    have hi':=integrable_abs_product μ hn f hf hi
    have hpos (ω:Ω):0≤∏i,f i ω:=Finset.prod_nonneg (fun i _=>pow_nonneg (clip_nonneg hν _) _)
    simpa only[abs_of_nonneg (hpos _)] using hi'
  refine ⟨by simpa only[heprod] using hprodI,?_⟩
  simp_rw[heprod]
  rw[abs_of_nonneg (integral_nonneg (fun ω=>Finset.prod_nonneg (fun i _=>pow_nonneg (clip_nonneg hν _) _)))] at hh
  convert! hh using 1
  dsimp[r]
  rw[Finset.prod_pow]

theorem dominated_even_moment {Ω:Type*}[MeasurableSpace Ω](μ:Measure Ω)[IsProbabilityMeasure μ]
    {n:ℕ}(hn:0<n)(X:Fin n→Ω→ℝ)(hXm:∀i,Measurable (X i))(v:Fin n→ℝ≥0)
    (hX:∀i,HasLaw (X i) (gaussianReal 0 (v i)) μ){ν B:ℝ}(hν:0≤ν)(hB:0≤B)
    (R:Ω→ℝ)(hR:Measurable R)(hb:∀ω,|R ω|≤B*(∏i,clip ν (X i ω)))(p:ℕ):
    Integrable (fun ω=>|R ω|^(2*p)) μ ∧
      (∫ω,|R ω|^(2*p) ∂μ)≤clipMomentConstant (p*n)*(B*(∏i,min 1 (ν*sqrt (v i:ℝ))))^(2*p):=by
  have hm:=product_even_moment μ hn X hXm v hX hν p
  have hpow (ω:Ω):|R ω|^(2*p)≤B^(2*p)*|∏i,clip ν (X i ω)|^(2*p):=by
    rw[abs_of_nonneg (Finset.prod_nonneg (fun i _=>clip_nonneg hν _)),←mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hb ω) _
  have hi:Integrable (fun ω=>|R ω|^(2*p)) μ:=by
    apply (hm.1.const_mul _).mono' ((continuous_abs.measurable.comp hR).pow_const _).aestronglyMeasurable
    exact ae_of_all _ (fun ω=>by rw[Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (abs_nonneg _) _)];exact hpow ω)
  refine ⟨hi,?_⟩
  calc
    _≤∫ω,B^(2*p)*|∏i,clip ν (X i ω)|^(2*p) ∂μ:=integral_mono hi (hm.1.const_mul _) hpow
    _=B^(2*p)*(∫ω,|∏i,clip ν (X i ω)|^(2*p) ∂μ):=integral_const_mul _ _
    _≤B^(2*p)*(clipMomentConstant (p*n)*(∏i,min 1 (ν*sqrt (v i:ℝ)))^(2*p)):=
      mul_le_mul_of_nonneg_left hm.2 (pow_nonneg hB _)
    _=_:=by rw[mul_pow];ring

end SHE.GaussianClipProducts
