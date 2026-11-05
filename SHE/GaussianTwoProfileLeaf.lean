module

public import SHE.RoughLeafOffsetMoments
public import SHE.GaussianCenteredLeafMoments
public import SHE.GaussianProfile

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

/-! Endpoint rough moments under a different future covariance. -/
namespace SHE.GaussianTwoProfileLeaf
open Set MeasureTheory ProbabilityTheory Real GaussianAudit GaussianProfile
  GaussianCenteredLeafMoments RoughLeafOffsetMoments
open scoped NNReal

/-- The actual future Gaussian variance and the OWN endpoint profile
baseline variance may be unrelated. A common physical upper cap is
sufficient; no false variance ordering between the two profiles occurs. -/
theorem reference_baseline_even_moment {Ω:Type*}[MeasurableSpace Ω](μ:Measure Ω)[IsProbabilityMeasure μ]
    (X:Ω→ℝ)(hXm:Measurable X){v full cap:ℝ≥0}(hX:HasLaw X (gaussianReal 0 v) μ)
    (hv:v≤cap) (hfull:full≤cap)
    (a:ℝ→ℝ)(ha:Measurable a)(M H β:ℝ)(hM:∀z,|a z|≤M)(hH:0≤H)(hβ:0≤β)
    (hholder:∀z w,|a z-a w|≤H*|z-w|^β)(m:ℝ)(p:ℕ):
    Integrable (fun ω=>|a (m+X ω)-GaussianProfile.gaussianAverage a m full|^(2*p)) μ ∧
      (∫ω,|a (m+X ω)-GaussianProfile.gaussianAverage a m full|^(2*p) ∂μ)≤
        leafMomentConstant p β*(H*(cap:ℝ)^(β/2))^(2*p):=by
  let b:=GaussianProfile.gaussianAverage a m full
  have hbase:|a m-b|≤H*gaussianAbsMoment β*(full:ℝ)^(β/2):=by
    rw[abs_sub_comm]
    exact gaussianAverage_holder_displacement ha hM hH hβ full.coe_nonneg hholder m
  have hOff:Integrable (fun _:Ω=>|a m-b|^(2*p)) μ:=integrable_const _
  have hh:=gaussian_offset_even_moment μ a ha (fun _=>m) X (fun _=>b) measurable_const hXm measurable_const
    hX hH hβ hholder p hOff
  refine ⟨hh.1,hh.2.trans ?_⟩
  simp only[integral_const,probReal_univ,one_smul]
  have hr:(v:ℝ)^(β/2)≤(cap:ℝ)^(β/2):=
    rpow_le_rpow v.coe_nonneg (by exact_mod_cast hv) (by positivity)
  have hs:(H*(v:ℝ)^(β/2))^(2*p)≤(H*(cap:ℝ)^(β/2))^(2*p):=
    pow_le_pow_left₀ (mul_nonneg hH (rpow_nonneg v.coe_nonneg _))
      (mul_le_mul_of_nonneg_left hr hH) _
  have hfullpow : (full:ℝ)^(β/2)≤(cap:ℝ)^(β/2):=
    rpow_le_rpow full.coe_nonneg (by exact_mod_cast hfull) (by positivity)
  have hbcap : |a m-b|≤H*gaussianAbsMoment β*(cap:ℝ)^(β/2):=
    hbase.trans (mul_le_mul_of_nonneg_left hfullpow
      (mul_nonneg hH (gaussianAbsMoment_nonneg _)))
  have hbpow:|a m-b|^(2*p)≤(H*gaussianAbsMoment β*(cap:ℝ)^(β/2))^(2*p):=
    pow_le_pow_left₀ (abs_nonneg _) hbcap _
  have hg:=mul_le_mul_of_nonneg_left hs (gaussianAbsMoment_nonneg (((2*p:ℕ):ℝ)*β))
  have hp:=mul_le_mul_of_nonneg_left (add_le_add hg hbpow) (show 0≤(2:ℝ)^(2*p-1) by positivity)
  convert! hp using 1
  dsimp[leafMomentConstant]
  simp only[mul_pow]
  ring

/-- A displaced actual current mean is retained explicitly while the
future law belongs to one endpoint and the baseline to the other.
All random current dependence remains inside the original probability
measure; only the auxiliary increment has a Gaussian marginal. -/
theorem shifted_even_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X m : Ω→ℝ)
    (hXm : Measurable X) (hm : Measurable m) {v full cap : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) μ) (hv : v≤cap) (hfull : full≤cap)
    (a : ℝ→ℝ) (ha : Measurable a) (M H β : ℝ) (hM : ∀ z,|a z|≤M)
    (hH : 0≤H) (hβ : 0≤β) (hholder : ∀ z w,|a z-a w|≤H*|z-w|^β)
    (referenceMean : ℝ) (p : ℕ)
    (hi : Integrable (fun ω=>|m ω-referenceMean|^(((2*p:ℕ):ℝ)*β)) μ) :
    Integrable (fun ω=>|a (m ω+X ω)-GaussianProfile.gaussianAverage a referenceMean full|^(2*p)) μ ∧
      (∫ ω,|a (m ω+X ω)-GaussianProfile.gaussianAverage a referenceMean full|^(2*p) ∂μ)≤
        (2:ℝ)^(2*p-1)*(H^(2*p)*(∫ ω,|m ω-referenceMean|^(((2*p:ℕ):ℝ)*β) ∂μ)+
          leafMomentConstant p β*(H*(cap:ℝ)^(β/2))^(2*p)) := by
  have hbase:=reference_baseline_even_moment μ X hXm hX hv hfull a ha M H β hM hH hβ hholder referenceMean p
  have hh:=offset_even_moment μ a ha (fun ω=>referenceMean+X ω)
    (fun ω=>m ω-referenceMean) (fun _=>GaussianProfile.gaussianAverage a referenceMean full)
    (measurable_const.add hXm) (hm.sub_const _) measurable_const hH hβ hholder p hi hbase.1
  have he (ω : Ω) : referenceMean+X ω+(m ω-referenceMean)=m ω+X ω:=by ring
  simp only [he] at hh
  exact ⟨hh.1,hh.2.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hbase.2) (by positivity))⟩

end SHE.GaussianTwoProfileLeaf
