module

public import SHE.DefectTime

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

namespace SHE.DefectCombinedTime
open Set MeasureTheory Real

def kernel (Λ ρ bi bj τ:ℝ):ℝ:=newTimeKernel Λ 0 bi bj τ+
  Λ^(-ρ/2)*newTimeKernel Λ (ρ/2) bi bj τ

theorem nonneg {Λ ρ bi bj τ:ℝ}(hΛ:0≤Λ)(hbi:0≤bi)(hbj:0≤bj)(hτ:0≤τ):
    0≤kernel Λ ρ bi bj τ:=
  add_nonneg (newTimeKernel_nonneg hΛ hbi hbj hτ)
    (mul_nonneg (rpow_nonneg hΛ _) (newTimeKernel_nonneg hΛ hbi hbj hτ))

/-- The negative-output mass cancels the positive damping power of the
singular signed-input term. Arbitrary original endpoint offsets remain;
the resulting full new-time cost is only logarithmic. -/
theorem integral {Λ ρ bi bj H h:ℝ}(hΛ:0<Λ)(hρ:0<ρ)(hρ1:ρ≤1)
    (hbi:0≤bi)(hbj:0≤bj)(hH:0≤H)(hHh:H≤h):
    IntervalIntegrable (kernel Λ ρ bi bj) volume 0 H ∧
      (∫τ in (0:ℝ)..H,kernel Λ ρ bi bj τ)≤4+2/ρ+log (2+Λ*h):=by
  have h0:=newTimeKernel_intervalIntegrable hΛ.le hbi hbj hH
    (by norm_num:0≤(0:ℝ)) (by norm_num:(0:ℝ)≤1/2)
  have h1:=newTimeKernel_intervalIntegrable hΛ.le hbi hbj hH
    (half_pos hρ).le (by linarith:ρ/2≤1/2)
  have hi:IntervalIntegrable (kernel Λ ρ bi bj) volume 0 H:=h0.add (h1.const_mul _)
  refine ⟨hi,?_⟩
  unfold kernel
  rw [intervalIntegral.integral_add h0 (h1.const_mul _),intervalIntegral.integral_const_mul]
  have hp:=new_time_integral_power hΛ hbi hbj hH (half_pos hρ) (by linarith:ρ/2≤1/2)
  calc
    _≤(2+log (2+Λ*h))+Λ^(-ρ/2)*((2+1/(ρ/2))*Λ^(ρ/2)):=
      add_le_add (new_time_integral_log hΛ hbi hbj hH hHh)
        (mul_le_mul_of_nonneg_left hp (rpow_nonneg hΛ.le _))
    _=(2+log (2+Λ*h))+(2+1/(ρ/2))*(Λ^(-ρ/2)*Λ^(ρ/2)):=by ring
    _=4+2/ρ+log (2+Λ*h):=by
      rw [←rpow_add hΛ,show -ρ/2+ρ/2=0 by ring,rpow_zero,mul_one]
      ring

end SHE.DefectCombinedTime
