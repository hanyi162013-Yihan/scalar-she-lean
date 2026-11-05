module
public import SHE.DefectGapDyadicCost
public import SHE.FullMaster
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SHE.DefectGapClockDecay
open Filter Topology Real

def constant (ρ:ℝ)(k:ℕ):ℝ:=((1+k:ℕ):ℝ)^2*(4+2/ρ+log 3)

theorem clock_bound {Λ ρ:ℝ}(hΛ:1≤Λ)(hρ:0<ρ)(k:ℕ):
    DefectGapBandCost.clock Λ ρ k≤constant ρ k*(1+log Λ):=by
  have hΛp:0<Λ:=zero_lt_one.trans_le hΛ
  have hl:log (2+Λ)≤log 3+log Λ:=by
    have hh:=log_le_log (by linarith:0<2+Λ) (show 2+Λ≤3*Λ by linarith)
    rwa [log_mul (by norm_num:(3:ℝ)≠0) hΛp.ne'] at hh
  have hlog:0≤log Λ:=log_nonneg hΛ
  have h3:0≤log (3:ℝ):=log_nonneg (by norm_num)
  have hB:1≤4+2/ρ+log 3:=by have :=div_nonneg (by norm_num:(0:ℝ)≤2) hρ.le;linarith only [this,h3]
  have hp:log Λ≤(4+2/ρ+log 3)*log Λ:=(one_mul (log Λ)).symm.trans_le
    (mul_le_mul_of_nonneg_right hB hlog)
  unfold DefectGapBandCost.clock constant
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  nlinarith only [hl,hp]

/-- The common logarithmic first-defect clock factor is beaten by any
strictly positive high-frequency damping power. -/
theorem tends_zero {ρ a:ℝ}(hρ:0<ρ)(ha:0<a)(k:ℕ):
    Tendsto (fun Λ:ℝ=>DefectGapBandCost.clock Λ ρ k*Λ^(-a)) atTop (𝓝 0):=by
  have hlim:=logPower_mul_rpow_tends_zero ha 1
  have hu:Tendsto (fun Λ:ℝ=>constant ρ k*((1+log Λ)*Λ^(-a))) atTop (𝓝 0):=by
    simpa only [pow_one,mul_zero] using hlim.const_mul (constant ρ k)
  apply squeeze_zero' ?_ ?_ hu
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with Λ hΛ
    exact mul_nonneg (DefectGapBandCost.clock_nonneg (zero_le_one.trans hΛ) hρ k)
      (rpow_nonneg (zero_le_one.trans hΛ) _)
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with Λ hΛ
    have hh:=mul_le_mul_of_nonneg_right (clock_bound hΛ hρ k)
      (rpow_nonneg (zero_le_one.trans hΛ) (-a))
    exact hh.trans_eq (by ring)
end SHE.DefectGapClockDecay
