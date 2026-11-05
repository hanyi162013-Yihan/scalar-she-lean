module

public import SHE.HighFiniteRemainderDegree

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace SHE.HighFiniteRemainderDegree
open Real

/-- The actual `(1+frequency)` weight, including its genuine band
amplitude and all-frequency time loss, at the prescribed finite depth. -/
theorem one_add_frequency_decay {lam β η:ℝ} (hlam:1≤lam) (hβ:0<β) (hb:β≤4/25)
    (hη:0≤η) (hηb:η≤β/4):
    (lam^(-β))^2*(1+lam)^(2*(β/2+η))*
        (lam^(-3*β))^(((SHE.depth β:ℝ)*β-β/2-η)/2)≤
      (2:ℝ)^(2*(β/2+η))*lam^(-8:ℝ):=by
  have hl:0<lam:=zero_lt_one.trans_le hlam
  have ha:0≤2*(β/2+η):=by positivity
  have hp:(1+lam)^(2*(β/2+η))≤(2*lam)^(2*(β/2+η)):=
    rpow_le_rpow (by linarith) (by linarith) ha
  rw [mul_rpow (by norm_num:(0:ℝ)≤2) hl.le] at hp
  have hh:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (sq_nonneg (lam^(-β))))
    (rpow_nonneg (rpow_nonneg hl.le (-3*β)) (((SHE.depth β:ℝ)*β-β/2-η)/2))
  apply hh.trans
  have hm:=mul_le_mul_of_nonneg_left (frequency_decay hlam hβ hb hη hηb)
    (rpow_nonneg (by norm_num:(0:ℝ)≤2) (2*(β/2+η)))
  convert! hm using 1
  rw [←rpow_mul_natCast hl.le]
  have he:(-β)*(2:ℕ)=-2*β:=by norm_num;ring
  rw [he]
  ring

/-- The conservative R^-8 actual energy still leaves the printed
strict 5/2 margin after the Q-output contraction and Young inequality. -/
theorem final_rate_margin {β:ℝ} (hβ:0<β) (hb:β≤4/25):
    5/2<(SHE.rho β+8*(1/4:ℝ))/(1-β/2):=by
  have hd:0<1-β/2:=by linarith
  apply (lt_div_iff₀ hd).mpr
  unfold SHE.rho
  linarith

end SHE.HighFiniteRemainderDegree
