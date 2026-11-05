module

public import SHE.DyadicTransport
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE

/-- The exact square-level heat cancellation yields the scalar
generation majorant needed for Minkowski and the infinite dyadic sum. -/
theorem generation_sqrt_bound {E C t Λ ρ : ℝ} (r : ℕ)
    (hE : 0≤E) (hC : 0≤C) (ht : 0<t) (hΛ : 0≤Λ) (_hρ : 0≤ρ)
    (hb : E ≤ C*(2:ℝ)^r*(Λ+((2:ℝ)^r)^2)^ρ*
      min 1 (((2:ℝ)^r)⁻¹^2/(4*t))) :
    Real.sqrt E ≤ Real.sqrt C*DyadicTransport.massiveTerm (t^(-(1/2:ℝ))) Λ ρ r := by
  let D : ℝ := (2:ℝ)^r
  let a : ℝ := t^(-(1/2:ℝ))/D
  have hD : 0<D := by dsimp [D]; positivity
  have ha : 0≤a := by dsimp [a]; positivity
  have htinv : (t^(-(1/2:ℝ)))^2=t⁻¹ := by
    rw [← Real.rpow_mul_natCast ht.le]
    norm_num only [Nat.cast_ofNat]
    rw [Real.rpow_neg_one]
  have hv : D⁻¹^2/(4*t) ≤ a^2 := by
    have he : D⁻¹^2/(4*t)=a^2/4 := by
      dsimp [a]
      rw [div_pow,htinv]
      field_simp [hD.ne',ht.ne']
    rw [he]
    nlinarith only [sq_nonneg a]
  have hcap : min 1 (D⁻¹^2/(4*t)) ≤ (min 1 a)^2 := by
    by_cases ha1 : a≤1
    · rw [min_eq_right ha1]
      exact (min_le_right _ _).trans hv
    · rw [min_eq_left (le_of_lt (lt_of_not_ge ha1))]
      simpa only [one_pow] using min_le_left (1:ℝ) (D⁻¹^2/(4*t))
  have hm0 : 0≤DyadicTransport.massiveTerm (t^(-(1/2:ℝ))) Λ ρ r := by
    unfold DyadicTransport.massiveTerm
    positivity
  have hsq : (Real.sqrt C*DyadicTransport.massiveTerm (t^(-(1/2:ℝ))) Λ ρ r)^2 =
      C*D*(Λ+D^2)^ρ*(min 1 a)^2 := by
    rw [mul_pow,Real.sq_sqrt hC]
    unfold DyadicTransport.massiveTerm
    rw [mul_pow,mul_pow,← Real.rpow_mul_natCast (by positivity : 0≤Λ+((2:ℝ)^r)^2),
      ← Real.rpow_mul_natCast hD.le]
    norm_num only [Nat.cast_ofNat]
    rw [show ρ/2*2=ρ by ring,Real.rpow_one]
    change C*((min 1 a)^2*D*(Λ+D^2)^ρ)=_
    ring
  have hbound : E ≤ (Real.sqrt C*DyadicTransport.massiveTerm (t^(-(1/2:ℝ))) Λ ρ r)^2 := by
    rw [hsq]
    have hh := mul_le_mul_of_nonneg_left hcap (by positivity : 0≤C*D*(Λ+D^2)^ρ)
    exact hb.trans hh
  have hs := Real.sq_sqrt hE
  nlinarith only [hbound,hs,Real.sqrt_nonneg E,
    mul_nonneg (Real.sqrt_nonneg C) hm0]

/-- The constant Haar mode is the zeroth summand of the same actual
majorant on the small-time interval, with no cancellation assumed. -/
theorem constant_generation_sqrt_bound {E C t Λ ρ : ℝ}
    (_hE : 0≤E) (hC : 0≤C) (ht : 0<t) (ht1 : t≤1) (hΛ : 0≤Λ) (_hρ : 0≤ρ)
    (hb : E≤C*(Λ+1)^ρ) :
    Real.sqrt E ≤ Real.sqrt C*DyadicTransport.massiveTerm (t^(-(1/2:ℝ))) Λ ρ 0 := by
  have hA : 1≤t^(-(1/2:ℝ)) := by
    simpa using Real.rpow_le_rpow_of_nonpos ht ht1 (by norm_num : -(1/2:ℝ)≤0)
  have hm : DyadicTransport.massiveTerm (t^(-(1/2:ℝ))) Λ ρ 0=(Λ+1)^(ρ/2) := by
    simp only [DyadicTransport.massiveTerm,pow_zero,div_one,min_eq_left hA,
      Real.one_rpow,one_mul,one_pow]
  rw [hm]
  calc
    _ ≤ Real.sqrt (C*(Λ+1)^ρ) := Real.sqrt_le_sqrt hb
    _ = Real.sqrt C*(Λ+1)^(ρ/2) := by
      rw [Real.sqrt_mul hC]
      congr 1
      rw [Real.sqrt_eq_rpow,← Real.rpow_mul (by positivity : 0≤Λ+1)]
      congr 1
      ring

end SHE
