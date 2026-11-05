module

public import SHE.DependentProducts
public import SHE.MeasurableGaussianScores

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
noncomputable section

namespace SHE.GaussianEnvelopeMoments
open Set MeasureTheory ProbabilityTheory Real GaussianAudit GaussianIncrement
open scoped NNReal InnerProductSpace

/-- A genuine Gaussian projection envelope gives every even moment of
the dominated rough factor, including zero variance and exponent zero. -/
theorem dominated_even_moment {Ω:Type*}[MeasurableSpace Ω](μ:Measure Ω)
    (X F:Ω→ℝ){v:ℝ≥0}(hX:HasLaw X (gaussianReal 0 v) μ)(hF:Measurable F)
    {B β:ℝ}(_hB:0≤B)(hβ:0≤β)(hb:∀ω,|F ω|≤B*|X ω|^β)(p:ℕ):
    Integrable (fun ω=>|F ω|^(2*p)) μ ∧
      (∫ω,|F ω|^(2*p) ∂μ)≤gaussianAbsMoment (((2*p:ℕ):ℝ)*β)*(B*(v:ℝ)^(β/2))^(2*p):=by
  let q:=((2*p:ℕ):ℝ)*β
  have hq:0≤q:=by dsimp[q];positivity
  have hiX:Integrable (fun ω=>|X ω|^q) μ:=by
    convert! hX.integrable_comp (integrable_gaussian_abs_rpow v q hq) using 1
  have hmX:(∫ω,|X ω|^q ∂μ)=(v:ℝ)^(q/2)*gaussianAbsMoment q:=by
    have he:=hX.integral_comp (f:=fun z:ℝ=>|z|^q) (by fun_prop)
    change (∫ω,|X ω|^q ∂μ)=(∫z:ℝ,|z|^q ∂gaussianReal 0 v) at he
    rw[he,gaussian_abs_rpow_moment v q hq]
  have hpow (ω:Ω):|F ω|^(2*p)≤B^(2*p)*|X ω|^q:=by
    have hh:=pow_le_pow_left₀ (abs_nonneg (F ω)) (hb ω) (2*p)
    rw[mul_pow] at hh
    have he:(|X ω|^β)^(2*p)=|X ω|^q:=by
      rw[←Real.rpow_natCast,←Real.rpow_mul (abs_nonneg _)]
      congr 1
      dsimp[q]
      ring
    rwa[he] at hh
  have hi:Integrable (fun ω=>|F ω|^(2*p)) μ:=by
    apply (hiX.const_mul (B^(2*p))).mono' (by fun_prop)
    exact ae_of_all _ (fun ω=>by
      rw[Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact hpow ω)
  refine ⟨hi,?_⟩
  have hvpow:(v:ℝ)^(q/2)=((v:ℝ)^(β/2))^(2*p):=by
    rw[←Real.rpow_natCast,←Real.rpow_mul v.coe_nonneg]
    congr 1
    dsimp[q]
    ring
  calc
    _≤∫ω,B^(2*p)*|X ω|^q ∂μ:=integral_mono hi (hiX.const_mul _) hpow
    _=B^(2*p)*((v:ℝ)^(q/2)*gaussianAbsMoment q):=by rw[integral_const_mul,hmX]
    _=_:=by rw[hvpow,mul_pow];ring

theorem projection_hasLaw {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
    [MeasurableSpace E][BorelSpace E](μ:Measure E)[IsGaussian μ](L:E→L[ℝ] ℝ)
    (hL:∫y,L y ∂μ=0):HasLaw L (gaussianReal 0 (Var[L;μ]).toNNReal) μ:=by
  have hh:=centered_projection_hasLaw μ L
  convert! hh using 1
  funext y
  rw[hL,sub_zero]

theorem projection_envelope_moment {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
    [MeasurableSpace E][BorelSpace E](μ:Measure E)[IsGaussian μ](L:E→L[ℝ] ℝ)
    (hL:∫y,L y ∂μ=0)(F:E→ℝ)(hF:Measurable F){B β:ℝ}(hB:0≤B)(hβ:0≤β)
    (hb:∀y,|F y|≤B*|L y|^β)(p:ℕ):
    Integrable (fun y=>|F y|^(2*p)) μ ∧
      (∫y,|F y|^(2*p) ∂μ)≤gaussianAbsMoment (((2*p:ℕ):ℝ)*β)*(B*Var[L;μ]^(β/2))^(2*p):=by
  simpa only[Real.coe_toNNReal _ (variance_nonneg L μ)] using
    dominated_even_moment μ L F (projection_hasLaw μ L hL) hF hB hβ hb p

end SHE.GaussianEnvelopeMoments
