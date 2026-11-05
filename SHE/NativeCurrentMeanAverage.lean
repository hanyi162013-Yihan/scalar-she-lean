module

public import SHE.MixedPastNativePacketBounds
public import SHE.ScoreSpatialCauchy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.NativeCurrentMeanAverage
open Set MeasureTheory Real
variable {Θ:Type*} [MeasurableSpace Θ] (τ:Measure Θ) [IsProbabilityMeasure τ]

/-- The literal current score is averaged BEFORE its outer stochastic
estimate. Cauchy in theta produces exactly the integrated score
amplitude, rather than a product of unrelated current moments. -/
theorem mean_cap (M V:Θ→ℝ) (hM:Measurable M) (hV:Measurable V)
    (hiV:Integrable V τ) (hV0:∀θ,0≤V θ) {S G:ℝ} (hS:0≤S) (hG:0≤G)
    (hb:∀ᵐθ∂τ,|M θ|≤S*G*sqrt (V θ)):
    Integrable M τ ∧ |∫θ,M θ ∂τ|≤S*sqrt (∫θ,V θ ∂τ)*G:=by
  have hcs:=ScoreSpatialCauchy.weighted_sqrt_integral τ (fun _=>1) V
    (integrable_const 1) (by simpa only [one_mul] using hiV) hV
    (ae_of_all _ (fun _=>show 0≤(1:ℝ) by norm_num)) hV0
  have hs:Integrable (fun θ=>sqrt (V θ)) τ:=by simpa only [one_mul] using hcs.1
  have hbnd:(∫θ,sqrt (V θ) ∂τ)≤sqrt (∫θ,V θ ∂τ):=by
    simpa only [one_mul,integral_const,probReal_univ,one_smul,Real.sqrt_one] using hcs.2
  have hMi:Integrable M τ:=(hs.const_mul (S*G)).mono' hM.aestronglyMeasurable
    (hb.mono (fun θ hθ=>by simpa only [Real.norm_eq_abs] using hθ))
  refine ⟨hMi,?_⟩
  have hh:|∫θ,M θ ∂τ|≤∫θ,S*G*sqrt (V θ) ∂τ:=by
    simpa only [Real.norm_eq_abs] using norm_integral_le_of_norm_le (f:=M)
      (hs.const_mul (S*G)) (hb.mono (fun θ hθ=>by simpa only [Real.norm_eq_abs] using hθ))
  rw [integral_const_mul] at hh
  exact (hh.trans (mul_le_mul_of_nonneg_left hbnd (mul_nonneg hS hG))).trans_eq (by ring)

end SHE.NativeCurrentMeanAverage
