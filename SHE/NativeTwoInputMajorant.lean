module

public import SHE.NativeCurrentBudgetFrequency
public import SHE.NativeHigherEnergyFactors

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.NativeTwoInputMajorant
open Real

/-- Exact two-input scalar domination of the actual old-time averaged
native row. The current energy stays at q and the past energy stays at v;
neither displacement is replaced by a supremum. -/
theorem square_bound (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(Cs:ℕ→ℝ)
    (k:ℕ)(T w s ρ χ ν A0 Ccur Cpast Eq Ev:ℝ)
    (hT:0<T)(hT1:T≤1)(hw:0<w)(hs:0<s)(hEq:0≤Eq)(hEv:0≤Ev):
    2*(w^(ρ/2)*(Ccur*Eq^(χ/2)*
      QuarterRMSTimeFactors.oldTimeBudget P ell Cs k T (T-w) ((2-χ)/4) A0 ν+
      Cpast*sqrt Ev*s^(-(1/4:ℝ))*
      QuarterRMSTimeFactors.oldTimeBudget P ell Cs k T (T-w) (1/2:ℝ) A0 ν))^2≤
      4*A0^2*(Ccur^2*Eq^χ*NativeCurrentBudgetFrequency.majorant P ell Cs k ρ χ ν w^2+
        Cpast^2*Ev*s^(-(1/2:ℝ))*NativeCurrentBudgetFrequency.majorant P ell Cs k ρ 0 ν w^2):=by
  let Bc:=QuarterRMSTimeFactors.oldTimeBudget P ell Cs k T (T-w) ((2-χ)/4) A0 ν
  let Bp:=QuarterRMSTimeFactors.oldTimeBudget P ell Cs k T (T-w) (1/2:ℝ) A0 ν
  let Gc:=NativeCurrentBudgetFrequency.majorant P ell Cs k ρ χ ν w
  let Gp:=NativeCurrentBudgetFrequency.majorant P ell Cs k ρ 0 ν w
  have hc: (w^(ρ/2)*Bc)^2≤A0^2*Gc^2:=by
    have hh:=pow_le_pow_left₀ (abs_nonneg _) (NativeCurrentBudgetFrequency.budget_le P ell Cs k ρ χ ν T A0 hT hT1 hw) 2
    simpa only [mul_pow,sq_abs] using hh
  have hp: (w^(ρ/2)*Bp)^2≤A0^2*Gp^2:=by
    have hh:=pow_le_pow_left₀ (abs_nonneg _) (NativeCurrentBudgetFrequency.budget_le P ell Cs k ρ 0 ν T A0 hT hT1 hw) 2
    norm_num only [sub_zero,show (2:ℝ)/4=1/2 by norm_num] at hh
    simpa only [mul_pow,sq_abs] using hh
  let a:=Ccur*Eq^(χ/2)
  let b:=Cpast*sqrt Ev*s^(-(1/4:ℝ))
  let x:=a*(w^(ρ/2)*Bc)
  let y:=b*(w^(ρ/2)*Bp)
  have hx:x^2≤a^2*A0^2*Gc^2:=by
    dsimp only [x]
    rw [mul_pow]
    convert! mul_le_mul_of_nonneg_left hc (sq_nonneg a) using 1 <;> ring
  have hy:y^2≤b^2*A0^2*Gp^2:=by
    dsimp only [y]
    rw [mul_pow]
    convert! mul_le_mul_of_nonneg_left hp (sq_nonneg b) using 1 <;> ring
  have ha:a^2=Ccur^2*Eq^χ:=by
    dsimp only [a]
    rw [mul_pow,←Real.rpow_mul_natCast hEq]
    congr 2
    ring
  have hb:b^2=Cpast^2*Ev*s^(-(1/2:ℝ)):=by
    dsimp only [b]
    rw [mul_pow,mul_pow,Real.sq_sqrt hEv,NativeHigherEnergyFactors.quarter_power hs.le]
  calc
    _=2*(x+y)^2:=by dsimp only [x,y,a,b,Bc,Bp];congr 1;ring
    _≤4*(x^2+y^2):=by nlinarith [sq_nonneg (x-y)]
    _≤4*(a^2*A0^2*Gc^2+b^2*A0^2*Gp^2):=mul_le_mul_of_nonneg_left (add_le_add hx hy) (by norm_num)
    _=_:=by rw [ha,hb];dsimp only [Gc,Gp];ring

end SHE.NativeTwoInputMajorant
