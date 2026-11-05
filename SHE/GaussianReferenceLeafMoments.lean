module

public import SHE.RoughLeafOffsetMoments
public import SHE.GaussianCenteredLeafMoments
public import SHE.GaussianProfile

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

/-! Foreign old-coordinate suppression reduces the Gaussian marginal,
but leaves the full profile baseline unchanged. The same rough gain
survives, using covariance domination and the common physical mean. -/
namespace SHE.GaussianReferenceLeafMoments
open Set MeasureTheory ProbabilityTheory Real GaussianAudit GaussianProfile
  GaussianCenteredLeafMoments RoughLeafOffsetMoments
open scoped NNReal

theorem reference_baseline_even_moment {Ω:Type*}[MeasurableSpace Ω](μ:Measure Ω)[IsProbabilityMeasure μ]
    (X:Ω→ℝ)(hXm:Measurable X){v full:ℝ≥0}(hX:HasLaw X (gaussianReal 0 v) μ)(hv:v≤full)
    (a:ℝ→ℝ)(ha:Measurable a)(M H β:ℝ)(hM:∀z,|a z|≤M)(hH:0≤H)(hβ:0≤β)
    (hholder:∀z w,|a z-a w|≤H*|z-w|^β)(m:ℝ)(p:ℕ):
    Integrable (fun ω=>|a (m+X ω)-GaussianProfile.gaussianAverage a m full|^(2*p)) μ ∧
      (∫ω,|a (m+X ω)-GaussianProfile.gaussianAverage a m full|^(2*p) ∂μ)≤
        leafMomentConstant p β*(H*(full:ℝ)^(β/2))^(2*p):=by
  let b:=GaussianProfile.gaussianAverage a m full
  have hbase:|a m-b|≤H*gaussianAbsMoment β*(full:ℝ)^(β/2):=by
    rw[abs_sub_comm]
    exact gaussianAverage_holder_displacement ha hM hH hβ full.coe_nonneg hholder m
  have hOff:Integrable (fun _:Ω=>|a m-b|^(2*p)) μ:=integrable_const _
  have hh:=gaussian_offset_even_moment μ a ha (fun _=>m) X (fun _=>b) measurable_const hXm measurable_const
    hX hH hβ hholder p hOff
  refine ⟨hh.1,hh.2.trans ?_⟩
  simp only[integral_const,probReal_univ,one_smul]
  have hr:(v:ℝ)^(β/2)≤(full:ℝ)^(β/2):=
    rpow_le_rpow v.coe_nonneg (by exact_mod_cast hv) (by positivity)
  have hs:(H*(v:ℝ)^(β/2))^(2*p)≤(H*(full:ℝ)^(β/2))^(2*p):=
    pow_le_pow_left₀ (mul_nonneg hH (rpow_nonneg v.coe_nonneg _))
      (mul_le_mul_of_nonneg_left hr hH) _
  have hbpow:|a m-b|^(2*p)≤(H*gaussianAbsMoment β*(full:ℝ)^(β/2))^(2*p):=
    pow_le_pow_left₀ (abs_nonneg _) hbase _
  have hg:=mul_le_mul_of_nonneg_left hs (gaussianAbsMoment_nonneg (((2*p:ℕ):ℝ)*β))
  have hp:=mul_le_mul_of_nonneg_left (add_le_add hg hbpow) (show 0≤(2:ℝ)^(2*p-1) by positivity)
  convert! hp using 1
  dsimp[leafMomentConstant]
  simp only[mul_pow]
  ring

end SHE.GaussianReferenceLeafMoments
