module
public import SHE.NativeHeatSpan
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.NativeCircleDistance
open Real NativeHeatSpan StoppedFourier
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩

theorem norm_scale(x:HeatCircle):‖x‖=(2*Real.pi)*‖unitCenter x‖:=by
  induction x using Quotient.inductionOn with
  | _ r =>
    have hp:0<2*Real.pi:=by positivity
    change ‖(r:HeatCircle)‖=(2*Real.pi)*‖unitCenter (r:HeatCircle)‖
    rw [unitCenter,CircleNormalization.scale,AddCircle.equivAddCircle_apply_mk,
      AddCircle.norm_eq' (2*Real.pi) hp,AddCircle.norm_eq' 1 zero_lt_one]
    simp only [inv_one,mul_one,one_mul,mul_comm r ((2*Real.pi)⁻¹)]

theorem dist_scale(x y:HeatCircle):dist x y=(2*Real.pi)*dist (unitCenter x) (unitCenter y):=by
  simpa only [dist_eq_norm,unitCenter,map_sub] using norm_scale (x-y)

theorem sqrt_clock{t:ℝ}(ht:0≤t):sqrt (clock t)=sqrt t/(2*Real.pi):=by
  rw [clock,Real.sqrt_div ht]
  congr 1
  rw [show 4*Real.pi^2=(2*Real.pi)^2 by ring,Real.sqrt_sq (by positivity)]

end SHE.NativeCircleDistance
