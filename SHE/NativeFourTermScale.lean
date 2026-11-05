module

public import SHE.MixedNativeInputEnergyClock

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace SHE.NativeFourTermScale
open Real
open scoped ENNReal

private theorem ofReal_four (a b c d:ℝ)(ha:0≤a)(hb:0≤b)(hc:0≤c):
    ENNReal.ofReal (a*b*c*d)=ENNReal.ofReal a*ENNReal.ofReal b*ENNReal.ofReal c*ENNReal.ofReal d:=by
  rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg ha hb) hc),
    ENNReal.ofReal_mul (mul_nonneg ha hb),ENNReal.ofReal_mul ha]

/-- Exact band scaling of the four physical nonnegative cap terms. -/
theorem ofReal_scaled (A ν β ε tail χ Ccur Cpast Cgood Cbad Eq Ev En s Gc Gp Gg Gb:ℝ)
    (hν:0<ν)(hEq:0≤Eq)(hEv:0≤Ev)(hEn:0≤En)(hs:0≤s)(hχ:0≤χ):
    ENNReal.ofReal
      (8*(A*ν^(-β))^2*(Ccur^2*Eq^χ*Gc^2+Cpast^2*Ev*s^(-(1/2:ℝ))*Gp^2)+
        4*(A*ν^(-β))^2*(Cgood^2*ν^(2*ε)*En*Gg^2+Cbad^2*ν^(-tail)*Gb^2))=
    ENNReal.ofReal (8*A^2*Ccur^2)*ENNReal.ofReal (ν^(-2*β))*ENNReal.ofReal (Gc^2)*(ENNReal.ofReal Eq)^χ+
    ENNReal.ofReal (8*A^2*Cpast^2)*ENNReal.ofReal (ν^(-2*β))*
      ENNReal.ofReal (s^(-(1/2:ℝ))*Gp^2)*ENNReal.ofReal Ev+
    ENNReal.ofReal (4*A^2*Cgood^2)*ENNReal.ofReal (ν^(-2*β+2*ε))*ENNReal.ofReal (Gg^2)*ENNReal.ofReal En+
    ENNReal.ofReal (4*A^2*Cbad^2)*ENNReal.ofReal (ν^(-2*β-tail))*ENNReal.ofReal (Gb^2):=by
  have hA:(A*ν^(-β))^2=A^2*ν^(-2*β):=by
    rw [mul_pow,←rpow_mul_natCast hν.le]
    congr 1
    ring
  have he:8*(A*ν^(-β))^2*(Ccur^2*Eq^χ*Gc^2+Cpast^2*Ev*s^(-(1/2:ℝ))*Gp^2)+
      4*(A*ν^(-β))^2*(Cgood^2*ν^(2*ε)*En*Gg^2+Cbad^2*ν^(-tail)*Gb^2)=
      (8*A^2*Ccur^2)*ν^(-2*β)*Gc^2*Eq^χ+
      (8*A^2*Cpast^2)*ν^(-2*β)*(s^(-(1/2:ℝ))*Gp^2)*Ev+
      (4*A^2*Cgood^2)*ν^(-2*β+2*ε)*Gg^2*En+
      (4*A^2*Cbad^2)*ν^(-2*β-tail)*Gb^2:=by
    rw [hA,show -2*β-tail=(-2*β)+(-tail) by ring,
      rpow_add hν,rpow_add hν]
    ring
  rw [he]
  rw [ENNReal.ofReal_add (by positivity),ENNReal.ofReal_add (by positivity),
    ENNReal.ofReal_add (by positivity)]
  rw [ofReal_four _ _ _ _ (by positivity) (by positivity) (by positivity),
    ofReal_four _ _ _ _ (by positivity) (by positivity) (by positivity),
    ofReal_four _ _ _ _ (by positivity) (by positivity) (by positivity)]
  rw [ENNReal.ofReal_mul (by positivity:0≤(4*A^2*Cbad^2)*ν^(-2*β-tail)),
    ENNReal.ofReal_mul (by positivity:0≤4*A^2*Cbad^2),
    ENNReal.ofReal_rpow_of_nonneg hEq hχ]
  all_goals positivity

end SHE.NativeFourTermScale
