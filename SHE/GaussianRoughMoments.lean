module

public import SHE.GaussianAudit
public import SHE.ProfileL2

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

/-! The actual centered rough Gaussian leaf gains its physical variance to
the Hölder power. No derivative of the coefficient is used. -/
namespace SHE.GaussianRoughMoments
open Set MeasureTheory ProbabilityTheory GaussianAudit ProfileL2 Real
open scoped NNReal

variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem centered_holder_leaf_sq (μ:Measure E) [IsGaussian μ] (L:E→L[ℝ] ℝ)
    (hL:∫y,L y ∂μ=0) (a:ℝ→ℝ) (ha:Measurable a) (M H β:ℝ)
    (hM:∀z,|a z|≤M) (hH:0≤H) (hβ:0≤β)
    (hholder:∀z w,|a z-a w|≤H*|z-w|^β) (m:ℝ):
    normTwo μ (fun y=>a (m+L y)-(∫z,a (m+L z) ∂μ))^2≤
      H^2*Var[L;μ]^β*gaussianAbsMoment (2*β):=by
  let f:E→ℝ:=fun y=>a (m+L y)
  have hfm:Measurable f:=ha.comp (by fun_prop)
  have hf:MemLp f 2 μ:=bounded_memLp hfm (fun y=>hM _)
  have hdiff:MemLp (fun y=>f y-a m) 2 μ:=hf.sub (memLp_const _)
  have hLaw:=centered_projection_hasLaw μ L
  have hLaw':HasLaw L (gaussianReal 0 (Var[L;μ]).toNNReal) μ:=by
    convert! hLaw using 1
    funext y
    rw[hL,sub_zero]
  have hiPow:Integrable (fun y=>|L y|^(2*β)) μ:=by
    convert! hLaw'.integrable_comp (integrable_gaussian_abs_rpow (Var[L;μ]).toNNReal (2*β) (by positivity)) using 1
  have hmom:(∫y,|L y|^(2*β) ∂μ)=Var[L;μ]^β*gaussianAbsMoment (2*β):=by
    have hi:=hLaw'.integral_comp (f:=fun z:ℝ=>|z|^(2*β)) (by fun_prop)
    change (∫y,|L y|^(2*β) ∂μ)=_ at hi
    rw[hi,gaussian_abs_rpow_moment _ _ (by positivity),Real.coe_toNNReal _ (variance_nonneg L μ)]
    congr 2
    ring
  have hv:Var[f;μ]≤∫y,(f y-a m)^2 ∂μ:=by
    rw[←variance_sub_const hf.aestronglyMeasurable (a m)]
    exact variance_le_expectation_sq hdiff.aestronglyMeasurable
  rw[normTwo_sq,←variance_eq_integral hf.aemeasurable]
  calc
    _≤∫y,(f y-a m)^2 ∂μ:=hv
    _≤∫y,H^2*|L y|^(2*β) ∂μ:=by
      apply integral_mono hdiff.integrable_sq (hiPow.const_mul _)
      intro y
      have hh:=hholder (m+L y) m
      rw[add_sub_cancel_left] at hh
      have hsq:|a (m+L y)-a m|^2≤(H*|L y|^β)^2:=
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hH (rpow_nonneg (abs_nonneg _) _))).mpr hh
      change (a (m+L y)-a m)^2≤H^2*|L y|^(2*β)
      have he:(|L y|^β)^2=|L y|^(2*β):=by
        rw[←Real.rpow_two,←Real.rpow_mul (abs_nonneg _)]
        congr 1
        ring
      rw[sq_abs,mul_pow,he] at hsq
      exact hsq
    _=_:=by rw[integral_const_mul,hmom];ring

end SHE.GaussianRoughMoments
