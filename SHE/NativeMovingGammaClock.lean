module
public import SHE.NativeGammaAgeValue
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.NativeMovingGammaClock
open Set MeasureTheory
open scoped NNReal
/-- Total moving-past clock, equal to the original past on its actual
integration interval. Its extension only makes all reference processes
well-typed outside that interval. -/
def base (W r:ℝ):ℝ:=min (max r 0) W
def past (W r:ℝ):ℝ≥0:=(base W r).toNNReal
def terminal (W h r:ℝ):ℝ≥0:=(base W r+h).toNNReal

theorem base_nonneg {W:ℝ} (hW:0≤W) (r:ℝ):0≤base W r:=
  le_min (le_max_right _ _) hW
theorem base_le (W r:ℝ):base W r≤W:=min_le_right _ _
theorem base_eq {W r:ℝ} (hr:r∈Ioc (0:ℝ) W):base W r=r:=by
  simp only [base,max_eq_left hr.1.le,min_eq_left hr.2]
theorem past_eq {W r:ℝ} (hr:r∈Ioc (0:ℝ) W):past W r=r.toNNReal:=by rw [past,base_eq hr]
theorem terminal_eq {W r:ℝ} (hr:r∈Ioc (0:ℝ) W) (h:ℝ):terminal W h r=(r+h).toNNReal:=by
  rw [terminal,base_eq hr]
theorem coe_past {W:ℝ} (hW:0≤W)(r:ℝ):(past W r:ℝ)=base W r:=
  Real.coe_toNNReal _ (base_nonneg hW r)
theorem coe_terminal {W h:ℝ} (hW:0≤W)(hh:0≤h)(r:ℝ):(terminal W h r:ℝ)=base W r+h:=
  Real.coe_toNNReal _ (add_nonneg (base_nonneg hW r) hh)
theorem span {W h:ℝ} (hW:0≤W)(hh:0≤h)(r:ℝ):
    (terminal W h r:ℝ)-(past W r:ℝ)=h:=by
  rw [coe_terminal hW hh,coe_past hW]
  ring
theorem past_lt {W h:ℝ}(hW:0≤W)(hh:0<h)(r:ℝ):past W r<terminal W h r:=by
  exact_mod_cast (show (past W r:ℝ)<(terminal W h r:ℝ) by
    rw [coe_past hW,coe_terminal hW hh.le];linarith)
theorem terminal_pos {W h:ℝ}(hW:0≤W)(hh:0<h)(r:ℝ):0<terminal W h r:=
  (show (0:ℝ≥0)≤past W r from zero_le).trans_lt (past_lt hW hh r)
theorem terminal_le {W h:ℝ}(hW:0≤W)(hh:0≤h)(H:ℝ≥0)(hcover:W+h≤H)(r:ℝ):
    terminal W h r≤H:=by
  exact_mod_cast (show (terminal W h r:ℝ)≤(H:ℝ) by
    rw [coe_terminal hW hh]
    linarith [base_le W r])
theorem past_measurable (W:ℝ):Measurable (past W):=
  measurable_real_toNNReal.comp ((measurable_id.max measurable_const).min measurable_const)
theorem terminal_measurable (W h:ℝ):Measurable (terminal W h):=
  measurable_real_toNNReal.comp (((measurable_id.max measurable_const).min measurable_const).add_const h)
end SHE.NativeMovingGammaClock
