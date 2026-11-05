module

public import SHE.OldFractionHeatScale
public import SHE.ProfileL2
public import SHE.RootConvolution

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! Exact scalar powers in the proved physical n=1 Gaussian heat-tree
estimate, and its two-endpoint time integration. The Gaussian spatial
estimate remains the explicit input in `physical_energy_to_power`; it is
proved for the literal word in NativeFirstWordHeatTree. -/
namespace SHE.FirstWordPowers
open Set MeasureTheory AddCircle Real StoppedFourier ProfileVariance NativeOldRoot
  HeatTorusKernel HeatTorus GaussianAudit OldFractionHeatScale ProfileL2
open scoped NNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩

def roughConstant (U H β:ℝ):ℝ:=sqrt (H^2*(upperConstant*U)^β*gaussianAbsMoment (2*β))

theorem roughConstant_nonneg (U H β:ℝ):0≤roughConstant U H β:=sqrt_nonneg _

theorem rough_gain_identity {s U:ℝ}(hs:0<s)(hU:0≤U)(H β:ℝ):
    sqrt (H^2*(upperConstant*U*s^(1/2:ℝ))^β*gaussianAbsMoment (2*β))=
      roughConstant U H β*s^(β/4):=by
  rw[Real.mul_rpow (mul_nonneg upperConstant_pos.le hU) (rpow_nonneg hs.le _),
    ←Real.rpow_mul hs.le]
  have he:H^2*((upperConstant*U)^β*s^((1/2:ℝ)*β))*gaussianAbsMoment (2*β)=
      (H^2*(upperConstant*U)^β*gaussianAbsMoment (2*β))*s^((1/2:ℝ)*β):=by ring
  rw[he,sqrt_mul (mul_nonneg (mul_nonneg (sq_nonneg _) (rpow_nonneg (mul_nonneg upperConstant_pos.le hU) _)) (gaussianAbsMoment_nonneg _)),
    Real.sqrt_eq_rpow (s^((1/2:ℝ)*β)),←Real.rpow_mul hs.le]
  unfold roughConstant
  congr 2
  ring

/-- The actual heat-tree square estimate has exactly root degree -1 and
new signed-input degree (β-1)/4 after inserting its literal old variance.
No limiting or endpoint convention is used in this algebraic conversion. -/
theorem physical_energy_to_power {X:Type*}[MeasurableSpace X](μ:Measure X)(G:X→ℝ)
    {ellOld ell C r s U H β A0 ν d:ℝ}
    (hellOld:0<ellOld)(hell:0<ell)(hC:0≤C)(hr:0<r)(hr1:r≤1)(hs:0<s)(hU:0≤U)
    (hA0:0≤A0)(hν:0≤ν)(hd:0≤d)
    (hE:(∫x,G x^2 ∂μ)≤‖unitHeatKernel (r/(4*π^2)) 0‖^4*
      (4*A0*rootClipMass (oldVariance ellOld r) ν*
        sqrt (H^2*(upperConstant*U*s^(1/2:ℝ))^β*gaussianAbsMoment (2*β)))^2*
      ((C/ell)*(sqrt s)⁻¹)*d^2):
    normTwo μ G≤4*A0*rootScaleConstant ellOld*roughConstant U H β*sqrt (C/ell)*
      SHE.rootKernel ν r*s^((β-1)/4)*d:=by
  let V:=‖unitHeatKernel (r/(4*π^2)) 0‖^2*rootClipMass (oldVariance ellOld r) ν
  have hV:0≤V:=mul_nonneg (sq_nonneg _) (rootClipMass_nonneg _ hν)
  have hroot:V≤rootScaleConstant ellOld*SHE.rootKernel ν r:=
    old_fraction_heat_root_bound hellOld hr hr1 hν
  have hcoef:0≤4*A0*roughConstant U H β*sqrt (C/ell)*s^((β-1)/4)*d:=by
    positivity [roughConstant_nonneg U H β]
  have hlin:4*A0*V*roughConstant U H β*sqrt (C/ell)*s^((β-1)/4)*d≤
      4*A0*(rootScaleConstant ellOld*SHE.rootKernel ν r)*roughConstant U H β*
        sqrt (C/ell)*s^((β-1)/4)*d:=by
    convert! mul_le_mul_of_nonneg_left hroot hcoef using 1 <;> ring
  have halg:‖unitHeatKernel (r/(4*π^2)) 0‖^4*
      (4*A0*rootClipMass (oldVariance ellOld r) ν*
        sqrt (H^2*(upperConstant*U*s^(1/2:ℝ))^β*gaussianAbsMoment (2*β)))^2*
      ((C/ell)*(sqrt s)⁻¹)*d^2=
      (4*A0*V*roughConstant U H β*sqrt (C/ell)*s^((β-1)/4)*d)^2:=by
    rw[rough_gain_identity hs hU H β]
    have hpow:(s^(β/4))^2*(sqrt s)⁻¹=(s^((β-1)/4))^2:=by
      rw[←Real.rpow_mul_natCast hs.le,←Real.rpow_mul_natCast hs.le,
        Real.sqrt_eq_rpow,←Real.rpow_neg hs.le,←Real.rpow_add hs]
      congr 1
      ring
    have hsq:sqrt (C/ell)^2=C/ell:=sq_sqrt (by positivity)
    dsimp only[V]
    simp only[mul_pow,hsq]
    linear_combination (4*A0)^2*‖unitHeatKernel (r/(4*π^2)) 0‖^4*
      rootClipMass (oldVariance ellOld r) ν^2*roughConstant U H β^2*(C/ell)*d^2*hpow
  have hE':normTwo μ G^2≤(4*A0*V*roughConstant U H β*sqrt (C/ell)*s^((β-1)/4)*d)^2:=by
    rw[normTwo_sq]
    exact hE.trans_eq halg
  have hN:0≤4*A0*V*roughConstant U H β*sqrt (C/ell)*s^((β-1)/4)*d:=by
    positivity [roughConstant_nonneg U H β]
  have hh: normTwo μ G≤4*A0*V*roughConstant U H β*sqrt (C/ell)*s^((β-1)/4)*d:=
    (sq_le_sq₀ (normTwo_nonneg _ _) hN).mp hE'
  convert! hh.trans hlin using 1
  ring

/-- The n=1 mean scalar ledger is integrable at both corners and has the
claimed time degree; the exact clipped root mass remains in the bound. -/
theorem firstWord_mean_time_degree {ν β h:ℝ}(hν:0≤ν)(hβ:0≤β)(hh:0<h):
    IntervalIntegrable (fun s:ℝ=>SHE.rootKernel ν (h-s)*s^((β-1)/4)) volume 0 h ∧
      (∫s in (0:ℝ)..h,SHE.rootKernel ν (h-s)*s^((β-1)/4))≤
        (2*(1+1/((β-1)/4+1)))*h^((β-1)/4)*SHE.rootMass ν h:=by
  have hB:0<(β-1)/4+1:=by linarith
  have hi:=SHE.root_power_pair_intervalIntegrable hν hB hh.le
  have hb:=SHE.root_power_convolution_le hν hB hh
  simp only[add_sub_cancel_right] at hi hb
  exact ⟨by convert! hi using 1;funext s;ring,by convert! hb using 1;congr 1;funext s;ring⟩

end SHE.FirstWordPowers
