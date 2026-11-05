module

public import SHE.GaussianEnvelopeMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.GaussianClipMoments
open Set MeasureTheory ProbabilityTheory Real GaussianAudit ProfileL2
open scoped NNReal

def clip (ν z:ℝ):ℝ:=min 1 (ν*|z|)
def clipMomentConstant (p:ℕ):ℝ:=max 1 (firstScoreMoment p)

theorem clip_nonneg {ν:ℝ}(hν:0≤ν)(z:ℝ):0≤clip ν z:=
  le_min (by norm_num) (mul_nonneg hν (abs_nonneg _))

theorem clipMomentConstant_nonneg (p:ℕ):0≤clipMomentConstant p:=by
  exact (by norm_num:0≤(1:ℝ)).trans (le_max_left _ _)

/-- Every fixed moment retains the full Bernstein clip. Correlation with
any scores or other increments is irrelevant to this marginal estimate. -/
theorem clip_even_moment {Ω:Type*}[MeasurableSpace Ω](μ:Measure Ω)[IsProbabilityMeasure μ]
    (X:Ω→ℝ)(hXm:Measurable X){v:ℝ≥0}(hX:HasLaw X (gaussianReal 0 v) μ)
    {ν:ℝ}(hν:0≤ν)(p:ℕ):
    Integrable (fun ω=>|clip ν (X ω)|^(2*p)) μ ∧
      (∫ω,|clip ν (X ω)|^(2*p) ∂μ)≤clipMomentConstant p*(min 1 (ν*sqrt (v:ℝ)))^(2*p):=by
  have hc:Measurable (fun ω=>clip ν (X ω)):=
    measurable_const.min (measurable_const.mul (continuous_abs.measurable.comp hXm))
  have hclip (ω:Ω):|clip ν (X ω)|≤1:=by
    rw[abs_of_nonneg (clip_nonneg hν _)]
    exact min_le_left _ _
  have hi:Integrable (fun ω=>|clip ν (X ω)|^(2*p)) μ:=
    (bounded_memLp (by fun_prop) (fun ω=>by
      rw[abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact (pow_le_pow_left₀ (abs_nonneg _) (hclip ω) _).trans_eq (one_pow _))).integrable (by norm_num)
  refine ⟨hi,?_⟩
  by_cases hsmall:ν*sqrt (v:ℝ)≤1
  · rw[min_eq_right hsmall]
    have hiX:Integrable (fun ω=>|X ω|^(2*p)) μ:=by
      have hh:Integrable (fun z:ℝ=>|z|^(2*p)) (gaussianReal 0 v):=by
        simpa only[pow_abs_two_mul] using integrable_gaussian_power v (2*p)
      convert! hX.integrable_comp hh using 1
    have hm:(∫ω,|X ω|^(2*p) ∂μ)=(v:ℝ)^p*firstScoreMoment p:=by
      have hh:=hX.integral_comp (f:=fun z:ℝ=>|z|^(2*p)) (by fun_prop)
      change (∫ω,|X ω|^(2*p) ∂μ)=_ at hh
      rw[hh]
      simp_rw[pow_abs_two_mul]
      exact gaussian_even_moment v p
    have hb (ω:Ω):|clip ν (X ω)|^(2*p)≤ν^(2*p)*|X ω|^(2*p):=by
      rw[abs_of_nonneg (clip_nonneg hν _),←mul_pow]
      exact pow_le_pow_left₀ (clip_nonneg hν _) (min_le_right _ _) _
    calc
      _≤∫ω,ν^(2*p)*|X ω|^(2*p) ∂μ:=integral_mono hi (hiX.const_mul _) hb
      _=firstScoreMoment p*(ν*sqrt (v:ℝ))^(2*p):=by
        rw[integral_const_mul,hm,mul_pow,pow_mul (sqrt (v:ℝ)) 2 p,sq_sqrt v.coe_nonneg]
        ring
      _≤_:=mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (mul_nonneg hν (sqrt_nonneg _)) _)
  · rw[min_eq_left (le_of_not_ge hsmall),one_pow,mul_one]
    have hh:(∫ω,|clip ν (X ω)|^(2*p) ∂μ)≤1:=by
      have hb (ω:Ω):|clip ν (X ω)|^(2*p)≤1:=by
        exact (pow_le_pow_left₀ (abs_nonneg _) (hclip ω) _).trans_eq (one_pow _)
      simpa only[integral_const,probReal_univ,one_smul] using integral_mono hi (integrable_const (1:ℝ)) hb
    exact hh.trans (le_max_left _ _)

end SHE.GaussianClipMoments
