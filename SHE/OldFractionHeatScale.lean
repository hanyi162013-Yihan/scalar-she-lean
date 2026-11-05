module

public import SHE.NativeOldRoot
public import SHE.ProfileVariance
public import SHE.HeatTorusKernel
public import SHE.Kernels

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! The old fixed scalar Gaussian fraction and squared physical heat edge
have exactly the clipped root time degree. Both variance and spatial mass
are actual physical heat integrals, rather than assigned scaling premises. -/
namespace SHE.OldFractionHeatScale
open Set MeasureTheory AddCircle Real StoppedFourier ProfileVariance NativeOldRoot
  HeatTorusKernel HeatTorus
open scoped NNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩

def oldVariance (ell r:ℝ):ℝ≥0:=(varianceMap (fun _=>ell) r 0).toNNReal

theorem oldVariance_bounds {ell r:ℝ}(hell:0<ell)(hr:0<r)(hr1:r≤1):
    lowerConstant*ell*r^(1/2:ℝ)≤(oldVariance ell r:ℝ) ∧
      (oldVariance ell r:ℝ)≤upperConstant*ell*r^(1/2:ℝ):=by
  have hh:=varianceMap_elliptic (c:=fun _=>ell) measurable_const hr hr1 hell.le hell.le
    (fun _ _ _=>le_rfl) (fun _ _ _=>le_rfl) (0:HeatCircle)
  have hV:0≤varianceMap (fun _=>ell) r 0:=
    (mul_nonneg (mul_nonneg lowerConstant_pos.le hell.le) (rpow_nonneg hr.le _)).trans hh.1
  simpa only[oldVariance,Real.coe_toNNReal _ hV] using hh

theorem oldVariance_pos {ell r:ℝ}(hell:0<ell)(hr:0<r)(hr1:r≤1):0<(oldVariance ell r:ℝ):=
  (mul_pos (mul_pos lowerConstant_pos hell) (rpow_pos_of_pos hr _)).trans_le (oldVariance_bounds hell hr hr1).1

private theorem clip_scale {k x:ℝ}(_hk:0≤k)(hx:0≤x):
    min 1 (k*x)≤max 1 k*min 1 x:=by
  by_cases hx1:x≤1
  · rw[min_eq_right hx1]
    exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hx)
  · rw[min_eq_left (le_of_not_ge hx1),mul_one]
    exact (min_le_left _ _).trans (le_max_left _ _)

def rootScaleConstant (ell:ℝ):ℝ:=
  (1+heatConstant)*(rootClipConstant/(lowerConstant*ell))*max 1 (sqrt (upperConstant*ell))

theorem rootScaleConstant_nonneg {ell:ℝ}(hell:0≤ell):0≤rootScaleConstant ell:=by
  unfold rootScaleConstant
  positivity [heatConstant_pos,rootClipConstant_nonneg,lowerConstant_pos]

/-- Exact old physical heat mass at Fourier-normalized unit-circle time. -/
theorem oldHeat_mass_bound {r:ℝ}(hr:0<r)(hr1:r≤1):
    ‖unitHeatKernel (r/(4*π^2)) 0‖^2≤(1+heatConstant)*r^(-(1/2:ℝ)):=by
  have hpi:4*π^2≠(0:ℝ):=by positivity
  have hnorm:‖unitHeatKernel (r/(4*π^2)) 0‖=‖circleHeat r (0:HeatCircle)‖:=by
    unfold unitHeatKernel
    rw[(CircleNormalization.pull 1 (2*π)).norm_map]
    have he:4*π^2*(r/(4*π^2))=r:=by field_simp
    rw[he]
    simp
  rw[hnorm]
  have hh:=circleHeat_norm_sq_bound hr (0:HeatCircle)
  have hone:1≤r^(-(1/2:ℝ)):=by
    simpa using rpow_le_rpow_of_nonpos hr hr1 (by norm_num:-(1/2:ℝ)≤0)
  nlinarith

/-- The clipped root density is derived from the actual old Gaussian score
and actual physical heat-square mass, with no formal power assignment. -/
theorem old_fraction_heat_root_bound {ell r ν:ℝ}(hell:0<ell)(hr:0<r)(hr1:r≤1)(hν:0≤ν):
    ‖unitHeatKernel (r/(4*π^2)) 0‖^2*rootClipMass (oldVariance ell r) ν≤
      rootScaleConstant ell*SHE.rootKernel ν r:=by
  let v:ℝ≥0:=oldVariance ell r
  have hv:0<(v:ℝ):=oldVariance_pos hell hr hr1
  have hv0:v≠0:=by exact_mod_cast hv.ne'
  have hlow:= (oldVariance_bounds hell hr hr1).1
  have hup:= (oldVariance_bounds hell hr hr1).2
  have hden:0<lowerConstant*ell*r^(1/2:ℝ):=by positivity [lowerConstant_pos]
  have hinv:(v:ℝ)⁻¹≤(lowerConstant*ell*r^(1/2:ℝ))⁻¹:=inv_anti₀ hden hlow
  have hsqrt:sqrt (v:ℝ)≤sqrt (upperConstant*ell)*r^(1/4:ℝ):=by
    have hh:=sqrt_le_sqrt hup
    rw[sqrt_mul (mul_nonneg upperConstant_pos.le hell.le)] at hh
    have he:sqrt (r^(1/2:ℝ))=r^(1/4:ℝ):=by
      rw[Real.sqrt_eq_rpow,←Real.rpow_mul hr.le];congr 1;norm_num
    rwa[he] at hh
  have hclip:min 1 (ν*sqrt (v:ℝ))≤max 1 (sqrt (upperConstant*ell))*min 1 (ν*r^(1/4:ℝ)):=by
    exact (min_le_min le_rfl (mul_le_mul_of_nonneg_left hsqrt hν)).trans
      (by simpa only[mul_assoc,mul_comm,mul_left_comm] using
        clip_scale (sqrt_nonneg (upperConstant*ell)) (mul_nonneg hν (rpow_nonneg hr.le _)))
  have hc:=rootClipMass_scaled_bound hv0 hν
  have hc':rootClipMass v ν≤
      (rootClipConstant/(lowerConstant*ell))*r^(-(1/2:ℝ))*
        (max 1 (sqrt (upperConstant*ell))*min 1 (ν*r^(1/4:ℝ))):=by
    have hinv':rootClipConstant/(v:ℝ)≤(rootClipConstant/(lowerConstant*ell))*r^(-(1/2:ℝ)):=by
      have hh:=mul_le_mul_of_nonneg_left hinv rootClipConstant_nonneg
      simpa only[div_eq_mul_inv,mul_inv_rev,Real.rpow_neg hr.le,mul_assoc,mul_comm,mul_left_comm] using hh
    exact hc.trans (mul_le_mul hinv' hclip (le_min (by norm_num) (mul_nonneg hν (sqrt_nonneg _))) (by positivity [rootClipConstant_nonneg,lowerConstant_pos]))
  have hh:=mul_le_mul (oldHeat_mass_bound hr hr1) hc' (rootClipMass_nonneg v hν)
    (by positivity [heatConstant_pos])
  convert! hh using 1
  unfold rootScaleConstant SHE.rootKernel
  rw[show r^(-(1:ℝ))=r^(-(1/2:ℝ))*r^(-(1/2:ℝ)) by
    rw[←Real.rpow_add hr];congr 1;ring]
  ring

end SHE.OldFractionHeatScale
