module

public import SHE.FiniteAssignmentMoments
public import SHE.CorrelatedTwoSourceAverage

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace SHE.FiniteFibreAverageEnergy
open Set MeasureTheory Real
open scoped BigOperators
variable {Y W ι:Type*} [MeasurableSpace Y] [MeasurableSpace W] [Fintype ι]

/-- An ACTUAL finite source sum may be averaged before taking energy.
All fibre integrability is derived from the joint L1 packets, so this
identity does not exchange conditionally divergent Gaussian terms. -/
theorem energy (μ:Measure Y) [SFinite μ] (ν:Measure W) [SFinite ν]
    (F:ι→Y×W→ℝ) (hF:∀i,Measurable (F i)) (hFi:∀i,Integrable (F i) (μ.prod ν))
    (B:ι→ℝ) (hAi:∀i,Integrable (fun y=>|∫w,F i (y,w) ∂ν|^2) μ)
    (hB:∀i,(∫y,|∫w,F i (y,w) ∂ν|^2 ∂μ)≤B i) (α:ℝ):
    let V:=fun z:Y×W=>α*∑i,F i z
    let A:=fun y=>∫w,V (y,w) ∂ν
    Integrable V (μ.prod ν) ∧ Integrable (fun y=>|A y|^2) μ ∧
      (∫y,|A y|^2 ∂μ)≤α^2*(Fintype.card ι:ℝ)*(∑i,B i):=by
  classical
  intro V A
  let G:ι→Y→ℝ:=fun i y=>∫w,F i (y,w) ∂ν
  have hG(i):Measurable (G i):=(hF i).stronglyMeasurable.integral_prod_right'.measurable
  have hv:Integrable V (μ.prod ν):=(integrable_finsetSum Finset.univ (fun i _=>hFi i)).const_mul α
  have he:∀ᵐ y ∂μ,A y=α*∑i,G i y:=by
    filter_upwards [ae_all_iff.mpr (fun i=>(hFi i).prod_right_ae)] with y hy
    change (∫w,α*∑i,F i (y,w) ∂ν)=_
    rw [integral_const_mul,integral_finsetSum _ (fun i _=>hy i)]
  have hs:=FiniteAssignmentMoments.moment_sum μ Finset.univ.toList G
    (fun i _=>hG i) 1 (by decide) (fun i _=>hAi i) B (fun i _=>hB i)
  have hsum:Integrable (fun y=>|∑i,G i y|^2) μ ∧
      (∫y,|∑i,G i y|^2 ∂μ)≤(Fintype.card ι:ℝ)*(∑i,B i):=by
    simpa only [mul_one,show 2*1-1=1 by decide,pow_one,Finset.length_toList,
      Finset.card_univ,Finset.sum_map_toList] using hs
  have hi:Integrable (fun y=>|α*∑i,G i y|^2) μ:=by
    simpa only [abs_mul,mul_pow,sq_abs] using hsum.1.const_mul (α^2)
  have hAi':Integrable (fun y=>|A y|^2) μ:=hi.congr
    (he.mono (fun y hy=>congrArg (fun r:ℝ=>|r|^2) hy.symm))
  refine ⟨hv,hAi',?_⟩
  rw [integral_congr_ae (he.mono (fun y hy=>by rw [hy]))]
  simp only [abs_mul,mul_pow,sq_abs,integral_const_mul]
  have hb:=mul_le_mul_of_nonneg_left hsum.2 (sq_nonneg α)
  simpa only [sq_abs,mul_assoc] using hb

end SHE.FiniteFibreAverageEnergy
