module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.DyadicBandEnergy
open Real

def scale (β ε Λ C A : ℝ) : ℝ:=A*Λ^(-ε)*sqrt ((2:ℝ)^β*|C|)

theorem scale_nonneg {β ε Λ C A : ℝ} (hΛ : 0≤Λ) (hA : 0≤A) :
    0≤scale β ε Λ C A:=mul_nonneg (mul_nonneg hA (rpow_nonneg hΛ _)) (sqrt_nonneg _)

/-- A root band of amplitude Aν^-β absorbs every smaller arbitrary
positive frequency loss. This leaves a genuine geometric energy tail. -/
theorem bound {E β ε Λ C A ν : ℝ} (hβ : 0≤β) (hΛ : 0≤Λ) (hν : 1≤ν)
    (hE : E≤(A*ν^(-β))^2*Λ^(-2*ε)*(1+ν)^β*C) :
    E≤scale β ε Λ C A^2*ν^(-β) := by
  have hνp : 0<ν:=zero_lt_one.trans_le hν
  have hbase : 1+ν≤2*ν:=by linarith
  have hpow : (1+ν)^β≤(2:ℝ)^β*ν^β:=by
    have hh:=rpow_le_rpow (by positivity : 0≤1+ν) hbase hβ
    rwa [mul_rpow (by norm_num) hνp.le] at hh
  have hpre : 0≤(A*ν^(-β))^2*Λ^(-2*ε):=mul_nonneg (sq_nonneg _) (rpow_nonneg hΛ _)
  have hp : (ν^(-β))^2*ν^β=ν^(-β):=by
    rw [←rpow_mul_natCast hνp.le,←rpow_add hνp]
    congr 1
    ring
  have hl : (Λ^(-ε))^2=Λ^(-2*ε):=by
    rw [←rpow_mul_natCast hΛ]
    congr 1
    ring
  have hC : 0≤(2:ℝ)^β*|C|:=mul_nonneg (rpow_nonneg (by norm_num) _) (abs_nonneg _)
  calc
    E≤(A*ν^(-β))^2*Λ^(-2*ε)*(1+ν)^β*|C|:=
      hE.trans (mul_le_mul_of_nonneg_left (le_abs_self C) (mul_nonneg hpre (rpow_nonneg (by positivity) _)))
    _≤(A*ν^(-β))^2*Λ^(-2*ε)*((2:ℝ)^β*ν^β)*|C|:=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hpre) (abs_nonneg _)
    _=A^2*Λ^(-2*ε)*((2:ℝ)^β*|C|)*((ν^(-β))^2*ν^β):=by ring
    _=_:=by rw [hp,scale,mul_pow,mul_pow,sq_sqrt hC,hl]
end SHE.DyadicBandEnergy
