module
public import SHE.TwoPointHeatTorus
public import SHE.NativeCircleDistance

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeTwoPointHeatGram
open Real StoppedFourier HeatTorusKernel NativeHeatSpan NativeCircleDistance
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩

/-- The actual native period-2pi heat Gram retains the exact physical
clock normalization. Arbitrary signed directions are allowed. -/
theorem separated_lower:
    ∃H:ℝ,0<H ∧ ∀t:ℝ,0<t→t≤H→∀x y:HeatCircle,
      4*sqrt t≤dist x y→∀u v:ℝ,
        (u^2+v^2)/(16*sqrt t)≤‖(u:ℂ)•circleHeat t x+(v:ℂ)•circleHeat t y‖^2:=by
  obtain ⟨h,hh,_,hlower⟩:=TwoPointHeatTorus.separated_lower
  refine ⟨4*Real.pi^2*h,by positivity,?_⟩
  intro t ht hth x y hsep u v
  have hclock:clock t≤h:=by
    apply (div_le_iff₀ (by positivity:0<4*Real.pi^2)).mpr
    simpa only [mul_comm] using hth
  have hs:4*sqrt (clock t)≤dist (unitCenter x) (unitCenter y):=by
    rw [NativeCircleDistance.sqrt_clock ht.le]
    have hd:=NativeCircleDistance.dist_scale x y
    have hd':dist x y/(2*Real.pi)=dist (unitCenter x) (unitCenter y):=by
      rw [hd]
      field_simp
    rw [←hd']
    convert div_le_div_of_nonneg_right hsep (by positivity:0≤2*Real.pi) using 1 <;> ring
  have hl:=hlower (clock t) (clock_pos ht) hclock (unitCenter x) (unitCenter y) hs u v
  have hn:‖(u:ℂ)•unitHeatKernel (clock t) (unitCenter x)+(v:ℂ)•unitHeatKernel (clock t) (unitCenter y)‖=
      ‖(u:ℂ)•circleHeat t x+(v:ℂ)•circleHeat t y‖:=by
    rw [←CircleNormalization.push.norm_map
      ((u:ℂ)•unitHeatKernel (clock t) (unitCenter x)+(v:ℂ)•unitHeatKernel (clock t) (unitCenter y)),
      map_add,map_smul,map_smul,push_unit_kernel,push_unit_kernel]
  rw [hn,NativeCircleDistance.sqrt_clock ht.le] at hl
  convert hl using 1
  congr 1
  field_simp
  <;> norm_num

end SHE.NativeTwoPointHeatGram
