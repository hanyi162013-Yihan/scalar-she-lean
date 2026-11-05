module
public import SHE.DefectGapBandCost
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.DefectGapDyadicCost
open Set MeasureTheory Real
open scoped BigOperators

def coefficient (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(C:ℕ→ℝ)
    (k:ℕ)(A η Λ ρ:ℝ):ℝ:=
  (A*DefectGapFrequency.constant P ell C k 1 η*(2:ℝ)^η)*DefectGapBandCost.clock Λ ρ k

/-- Full old/new first-defect convolution costs sum at every finite
order, with a geometric high-frequency gain. Each band may have its own
physical window, and constants are independent of those windows. -/
theorem series (P:CanonicalCovariance.ProfileParameters){ell Λ ρ A β η R:ℝ}
    (hell:0<ell)(hΛ:0<Λ)(hρ:0<ρ)(hρ1:ρ≤1)(C:ℕ→ℝ)(hC:∀j,0≤C j)(k:ℕ)
    (hA:0≤A)(hη:0<η)(hηβ:η<β)(hR:1≤R)
    (h:ℕ→ℝ)(hh:∀n,0<h n)(hh1:∀n,h n≤1):
    let g:=fun n:ℕ=>DefectGapMixture.cost P ell C Λ ρ (h n)
      (A*(R*(2:ℝ)^n)^(-β)) (R*(2:ℝ)^n) k
    Summable g ∧ (∑'n,g n)≤
      coefficient P ell C k A η Λ ρ*StateBands.geometricConstant (β-η)*R^(-(β-η)):=by
  intro g
  have hRp:0<R:=zero_lt_one.trans_le hR
  have hγ:0<β-η:=sub_pos.mpr hηβ
  have hK:=DefectGapFrequency.constant_nonneg P hell C hC k (by norm_num:0≤(1:ℝ)) hη
  have hD:0≤coefficient P ell C k A η Λ ρ:=by
    unfold coefficient
    exact mul_nonneg (mul_nonneg (mul_nonneg hA hK) (rpow_nonneg (by norm_num) _))
      (DefectGapBandCost.clock_nonneg hΛ.le hρ k)
  have hν(n:ℕ):1≤R*(2:ℝ)^n:=
    one_le_mul_of_one_le_of_one_le hR (one_le_pow₀ (by norm_num:(1:ℝ)≤2))
  have hn(n:ℕ):0≤g n:=DefectGapMixture.cost_nonneg P hell hΛ hρ hρ1 (hh n) C hC k
    (mul_nonneg hA (rpow_nonneg (mul_nonneg hRp.le (by positivity)) _))
    (zero_le_one.trans (hν n))
  have hb(n:ℕ):g n≤coefficient P ell C k A η Λ ρ*(R*(2:ℝ)^n)^(-(β-η)):=by
    have hb:=DefectGapBandCost.cost_le P (Λ:=Λ) (ρ:=ρ) (h:=h n) (β:=β) (η:=η)
      (ν:=R*(2:ℝ)^n) hell hΛ.le hρ C hC k (hh n).le (hh1 n) hA hη (hν n)
    exact hb.trans_eq (by unfold coefficient;ring)
  have hs:=StateBands.geometric_bands hγ hRp
  have hmajor:=hs.1.mul_left (coefficient P ell C k A η Λ ρ)
  have hg:=Summable.of_nonneg_of_le hn hb hmajor
  refine ⟨hg,?_⟩
  calc
    _≤∑'n,coefficient P ell C k A η Λ ρ*(R*(2:ℝ)^n)^(-(β-η)):=
      hg.tsum_le_tsum hb hmajor
    _=_:=by rw [tsum_mul_left,hs.2];ring
end SHE.DefectGapDyadicCost
