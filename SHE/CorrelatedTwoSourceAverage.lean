module

public import SHE.CorrelatedPositiveJoint

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace SHE.CorrelatedTwoSourceAverage
open Set MeasureTheory ProbabilityTheory Real
variable {Y W:Type*} [MeasurableSpace Y] [MeasurableSpace W]

/-- A literal extracted source is dominated by a true current input
and a true past-profile input. Holder is applied to EACH on the complete
sample/output space before the old-space average; all correlations and
all original second-moment smallness are retained. -/
theorem energy (μ:Measure Y) [IsProbabilityMeasure μ] (ν:Measure W) [IsProbabilityMeasure ν]
    (F S D0 D1:Y×W→ℝ) (hF:Measurable F) (hS:Measurable S)
    (hD0:Measurable D0) (hD1:Measurable D1)
    (H:W→ℝ) (hH:Measurable H) (hHi:Integrable H ν) (hH0:∀w,0≤H w)
    {χ δ a C E0 E1:ℝ} (hχ:0≤χ) (hχ1:χ<1) (hδ:0≤δ) (hδ1:δ<1)
    (ha:0≤a) (hC:0≤C) (hE0:0≤E0) (hE1:0≤E1)
    (p:ℕ) (hp:0<p) (ho0:1≤(p:ℝ)*(1-χ)) (ho1:1≤(p:ℝ)*(1-δ))
    (hi0:∀ᵐ w ∂ν,MemLp (fun y=>D0 (y,w)) 2 μ ∧ (∫y,D0 (y,w)^2 ∂μ)≤E0)
    (hi1:∀ᵐ w ∂ν,MemLp (fun y=>D1 (y,w)) 2 μ ∧ (∫y,D1 (y,w)^2 ∂μ)≤E1)
    (hMom:∀ᵐ w ∂ν,Integrable (fun y=>|F (y,w)|^(2*p)) μ ∧
      (∫y,|F (y,w)|^(2*p) ∂μ)≤C*(H w)^(2*p))
    (hbound:∀z,|S z|≤a*|D0 z|^χ+|D1 z|^δ):
    let G:=fun y=>∫w,S (y,w)*F (y,w) ∂ν
    Integrable (fun z=>S z*F z) (μ.prod ν) ∧
    Integrable (fun y=>|G y|^2) μ ∧
      (∫y,|G y|^2 ∂μ)≤2*C^(1/(p:ℝ))*(a^2*E0^χ+E1^δ)*(∫w,H w ∂ν)^2:=by
  intro G
  have hFa:Measurable (fun z=>|F z|):=continuous_abs.measurable.comp hF
  have h0:=CorrelatedPositiveJoint.energy μ ν (fun z=>|F z|) D0 hFa hD0 H hH hHi hH0
    hχ hχ1 hC hE0 p hp ho0 hi0 (by simpa only [abs_abs] using hMom)
  have h1:=CorrelatedPositiveJoint.energy μ ν (fun z=>|F z|) D1 hFa hD1 H hH hHi hH0
    hδ hδ1 hC hE1 p hp ho1 hi1 (by simpa only [abs_abs] using hMom)
  let V:Y×W→ℝ:=fun z=>S z*F z
  let Q0:Y×W→ℝ:=fun z=>|D0 z|^χ*|F z|
  let Q1:Y×W→ℝ:=fun z=>|D1 z|^δ*|F z|
  let U0:Y→ℝ:=fun y=>∫w,Q0 (y,w) ∂ν
  let U1:Y→ℝ:=fun y=>∫w,Q1 (y,w) ∂ν
  have hVm:Measurable V:=hS.mul hF
  have hdom(z):|V z|≤a*Q0 z+Q1 z:=by
    have hh:=mul_le_mul_of_nonneg_right (hbound z) (abs_nonneg (F z))
    simpa only [V,Q0,Q1,abs_mul,add_mul,mul_assoc] using hh
  have hVi:Integrable V (μ.prod ν):=(h0.1.const_mul a |>.add h1.1).mono' hVm.aestronglyMeasurable
    (ae_of_all _ hdom)
  have hu0(y):0≤U0 y:=integral_nonneg (fun w=>mul_nonneg (rpow_nonneg (abs_nonneg _) _) (abs_nonneg _))
  have hu1(y):0≤U1 y:=integral_nonneg (fun w=>mul_nonneg (rpow_nonneg (abs_nonneg _) _) (abs_nonneg _))
  have hpoint:∀ᵐ y ∂μ,|G y|≤a*U0 y+U1 y:=by
    filter_upwards [hVi.prod_right_ae,h0.1.prod_right_ae,h1.1.prod_right_ae] with y hiy hi0y hi1y
    have hh:=integral_mono_ae hiy.abs ((hi0y.const_mul a).add hi1y) (ae_of_all _ (fun w=>hdom (y,w)))
    have hn : |G y| ≤ ∫w,|V (y,w)| ∂ν := by
      simpa only [Real.norm_eq_abs,G,V] using
        (norm_integral_le_integral_norm (fun w=>V (y,w)))
    have hs : (∫w,|V (y,w)| ∂ν) ≤ a*U0 y+U1 y := by
      change (∫w,|V (y,w)| ∂ν) ≤ ∫w,(a*Q0 (y,w)+Q1 (y,w)) ∂ν at hh
      rw [integral_add (hi0y.const_mul a) hi1y,integral_const_mul] at hh
      exact hh
    exact hn.trans hs
  have hsquare:∀ᵐ y ∂μ,|G y|^2≤2*a^2*|U0 y|^2+2*|U1 y|^2:=by
    filter_upwards [hpoint] with y hy
    have h0y:=hu0 y
    have h1y:=hu1 y
    have hn:0≤a*U0 y+U1 y:=by positivity
    have hb:=pow_le_pow_left₀ (abs_nonneg (G y)) hy 2
    nlinarith [sq_abs (U0 y),sq_abs (U1 y),sq_nonneg (a*U0 y-U1 y)]
  have hmaj:Integrable (fun y=>2*a^2*|U0 y|^2+2*|U1 y|^2) μ:=
    (h0.2.1.const_mul _).add (h1.2.1.const_mul _)
  have hGm:Measurable G:=hVm.stronglyMeasurable.integral_prod_right'.measurable
  have hGi:Integrable (fun y=>|G y|^2) μ:=hmaj.mono'
    ((continuous_abs.measurable.comp hGm).pow_const 2).aestronglyMeasurable
    (hsquare.mono (fun y hy=>by simpa only [Real.norm_eq_abs,abs_pow,abs_abs] using hy))
  refine ⟨hVi,hGi,?_⟩
  have hb:=integral_mono_ae hGi hmaj hsquare
  rw [integral_add (h0.2.1.const_mul _) (h1.2.1.const_mul _),integral_const_mul,integral_const_mul] at hb
  apply hb.trans
  have ht:=add_le_add (mul_le_mul_of_nonneg_left h0.2.2 (by positivity : 0≤2*a^2))
    (mul_le_mul_of_nonneg_left h1.2.2 (by norm_num : (0:ℝ)≤2))
  convert! ht using 1 <;> ring

end SHE.CorrelatedTwoSourceAverage
