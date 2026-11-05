module

public import SHE.HighFiniteRemainderWeight

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace SHE.HighFiniteRemainderDegree
open Real

/-- The prescribed finite depth even allows a uniformly bounded
coarse root amplitude; no band amplitude gain is needed here. -/
theorem no_amplitude_degree {β η:ℝ} (hβ:0<β) (hb:β≤4/25)
    (hη:0≤η) (hηb:η≤β/4):
    2*(β/2+η)-(3*β/2)*((SHE.depth β:ℝ)*β-β/2-η)≤-8:=by
  have hp:6≤(SHE.depth β:ℝ)*β^2:=(div_le_iff₀ (sq_pos_of_pos hβ)).mp (SHE.depth_lower β)
  have hηmul:β*η≤β*(β/4):=mul_le_mul_of_nonneg_left hηb hβ.le
  have hβ2:β^2≤(4/25:ℝ)^2:=sq_le_sq₀ hβ.le (by norm_num) |>.mpr hb
  nlinarith

/-- The true 1+frequency weight at h=frequency^(-3 beta),
with uniformly bounded root amplitude, decays by at least R^-8. -/
theorem no_amplitude_frequency_decay {lam β η:ℝ} (hlam:1≤lam) (hβ:0<β) (hb:β≤4/25)
    (hη:0≤η) (hηb:η≤β/4):
    (1+lam)^(2*(β/2+η))*(lam^(-3*β))^(((SHE.depth β:ℝ)*β-β/2-η)/2)≤
      (2:ℝ)^(2*(β/2+η))*lam^(-8:ℝ):=by
  have hl:0<lam:=zero_lt_one.trans_le hlam
  have ha:0≤2*(β/2+η):=by positivity
  have hp:(1+lam)^(2*(β/2+η))≤(2*lam)^(2*(β/2+η)):=
    rpow_le_rpow (by linarith) (by linarith) ha
  rw [mul_rpow (by norm_num:(0:ℝ)≤2) hl.le] at hp
  have hh:=mul_le_mul_of_nonneg_right hp
    (rpow_nonneg (rpow_nonneg hl.le (-3*β)) (((SHE.depth β:ℝ)*β-β/2-η)/2))
  apply hh.trans
  have he:lam^(2*(β/2+η))*(lam^(-3*β))^(((SHE.depth β:ℝ)*β-β/2-η)/2)=
      lam^(2*(β/2+η)-(3*β/2)*((SHE.depth β:ℝ)*β-β/2-η)):=by
    rw [←rpow_mul hl.le,←rpow_add hl]
    congr 1
    ring
  have hbnd:=rpow_le_rpow_of_exponent_le hlam (no_amplitude_degree hβ hb hη hηb)
  have hm:=mul_le_mul_of_nonneg_left hbnd
    (rpow_nonneg (by norm_num:(0:ℝ)≤2) (2*(β/2+η)))
  calc
    _=(2:ℝ)^(2*(β/2+η))*(lam^(2*(β/2+η))*(lam^(-3*β))^(((SHE.depth β:ℝ)*β-β/2-η)/2)):=by ring
    _≤_:=by rw [he];exact hm

end SHE.HighFiniteRemainderDegree
