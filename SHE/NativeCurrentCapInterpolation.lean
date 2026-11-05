module

public import SHE.NativeFirstScoreNoiseComparison
public import SHE.NativeFirstWholeComplete
public import SHE.TwoFreshCompleteWord
public import SHE.PairedRoughBlocks
public import SHE.CorrelatedCurrentHolder

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SHE.NativeCurrentCapInterpolation
open Set MeasureTheory Real

/-- The consistent cap applies to the COMPLETE kernel change. Profile
and omitted-baseline terms are retained additively, before clipping the
linear current term. -/
theorem clip {T A B C χ:ℝ} (hA:0≤A) (hB:0≤B) (hC:0≤C)
    (hχ:0≤χ) (hχ1:χ≤1) (hlinear:|T|≤A+B) (hcap:|T|≤C):
    |T|≤A^χ*C^(1-χ)+B:=by
  have hmin:min (A+B) C≤min A C+B:=by
    rcases le_total A C with h|h
    · rw [min_eq_left h]
      exact min_le_left _ _
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans (le_add_of_nonneg_right hB)
  have hp:min A C≤A^χ*C^(1-χ):=by
    simpa only [Real.rpow_one] using
      (PairedRoughBlocks.min_rpow_le (β:=1) hA hC hχ hχ1)
  exact (le_min hlinear hcap).trans (hmin.trans (add_le_add hp le_rfl))

/-- Gaussian even-moment caps are extracted before the outer native
average; all random score/offset factors therefore remain correlated. -/
theorem root_cap {x C S:ℝ} (hC:0≤C) (hS:0≤S) (p:ℕ) (hp:0<p)
    (h:|x|^(2*p)≤C*S^(2*p)):
    |x|≤C^(1/((2*p:ℕ):ℝ))*S:=by
  have hpow:(C^(1/((2*p:ℕ):ℝ))*S)^(2*p)=C*S^(2*p):=by
    rw [mul_pow,←Real.rpow_mul_natCast hC]
    have hpR:((2*p:ℕ):ℝ)≠0:=by positivity
    rw [one_div_mul_cancel hpR,Real.rpow_one]
  apply le_of_pow_le_pow_left₀ (by omega:2*p≠0) (by positivity:0≤C^(1/((2*p:ℕ):ℝ))*S)
  rw [hpow]
  exact h

/-- One COMMON time/score scale is retained while the genuine current
score amplitude receives the fractional gain. The consistent packet is
formed from the two own-profile endpoints and the complete mean packet. -/
theorem packet_clip {T S D H P χ:ℝ} (hS:0≤S) (hD:0≤D) (hH:0≤H) (hP:0≤P)
    (hχ:0≤χ) (hχ1:χ≤1) (hlinear:|T|≤S*D*H+P) (hcap:|T|≤2*S*H):
    |T|≤2*S*(D^χ*H)+P:=by
  have hc:=clip (mul_nonneg (mul_nonneg hS hD) hH) hP (by positivity:0≤2*S*H) hχ hχ1 hlinear hcap
  have hex:(S*D*H)^χ*(2*S*H)^(1-χ)≤2*S*(D^χ*H):=by
    rw [Real.mul_rpow (mul_nonneg hS hD) hH,Real.mul_rpow hS hD,
      Real.mul_rpow (mul_nonneg (by norm_num:0≤(2:ℝ)) hS) hH,
      Real.mul_rpow (by norm_num:0≤(2:ℝ)) hS]
    have hs:S^χ*S^(1-χ)=S:=by
      rw [←Real.rpow_add_of_nonneg hS hχ (sub_nonneg.mpr hχ1)]
      norm_num
    have hh:H^χ*H^(1-χ)=H:=by
      rw [←Real.rpow_add_of_nonneg hH hχ (sub_nonneg.mpr hχ1)]
      norm_num
    have htwo:(2:ℝ)^(1-χ)≤2:=by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num:1≤(2:ℝ))
        (by linarith:1-χ≤1)
    calc
      _=(2:ℝ)^(1-χ)*(S^χ*S^(1-χ))*(H^χ*H^(1-χ))*D^χ:=by ring
      _=(2:ℝ)^(1-χ)*S*H*D^χ:=by rw [hs,hh]
      _≤2*S*H*D^χ:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htwo hS) hH) (rpow_nonneg hD _)
      _=_:=by ring
  exact hc.trans (add_le_add hex le_rfl)

end SHE.NativeCurrentCapInterpolation
