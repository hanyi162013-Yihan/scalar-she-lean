module

public import SHE.NativeRandomRows

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
namespace SHE.NativeRowProductEnergy
open MeasureTheory Set AddCircle StoppedFourier
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {T Ω:Type*} [MeasurableSpace T] [MeasurableSpace Ω]
variable (μ:Measure Ω) [IsProbabilityMeasure μ]

/-- Exact original sample/native-space energy of the actual bounded
scalar rows, BEFORE any spatial output contraction. -/
theorem difference (F G:(T×Ω)×HeatCircle→ℂ) (hF:Measurable F) (hG:Measurable G)
    {B C:ℝ} (hFB:∀p x,‖F (p,x)‖≤B) (hGC:∀p x,‖G (p,x)‖≤C) (t:T):
    Integrable (fun z:Ω×HeatCircle=>‖F ((t,z.1),z.2)-G ((t,z.1),z.2)‖^2) (μ.prod haarAddCircle) ∧
      (∫ω,‖NativeRandomRows.nativeRow F (t,ω)-NativeRandomRows.nativeRow G (t,ω)‖^2 ∂μ)=
        ∫z:Ω×HeatCircle,‖F ((t,z.1),z.2)-G ((t,z.1),z.2)‖^2 ∂μ.prod haarAddCircle:=by
  have hmap:Measurable (fun z:Ω×HeatCircle=>((t,z.1),z.2)):=
    (measurable_const.prodMk measurable_fst).prodMk measurable_snd
  have hm:Measurable (fun z:Ω×HeatCircle=>‖F ((t,z.1),z.2)-G ((t,z.1),z.2)‖^2):=
    (((hF.comp hmap).sub (hG.comp hmap)).norm).pow_const 2
  have hi:Integrable (fun z:Ω×HeatCircle=>‖F ((t,z.1),z.2)-G ((t,z.1),z.2)‖^2) (μ.prod haarAddCircle):=by
    apply (integrable_const ((B+C)^2)).mono' hm.aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (add_le_add (hFB _ _) (hGC _ _))) 2
  refine ⟨hi,?_⟩
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards with ω
  rw [L2_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (NativeRandomRows.nativeRow F (t,ω)) (NativeRandomRows.nativeRow G (t,ω)),
    NativeRandomRows.nativeRow_ae hF hFB (t,ω),NativeRandomRows.nativeRow_ae hG hGC (t,ω)] with x hx hfx hgx
  rw [hx,Pi.sub_apply,hfx,hgx]

end SHE.NativeRowProductEnergy
