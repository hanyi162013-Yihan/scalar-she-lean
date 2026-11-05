module
public import SHE.BoundedHaarAnalysisContinuity

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SHE.NativeRowFieldContinuity
open Set MeasureTheory AddCircle FiniteHaar StoppedFourier NativeObservationCovariance NativeRowTargetContinuity
open scoped ENNReal NNReal
local instance unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance sigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance borelInst : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩

theorem heat_bound {t:ℝ}(ht:0<t)(x:HeatCircle):
    ∀ᵐy∂haarAddCircle,‖circleHeat t x y‖≤1+heatConstant*(t/2)^(-(1/2:ℝ)):=by
  filter_upwards [ProfileVariance.heatPhysical_ae ht x] with y hy
  rw [←hy,←WordRecursion.heatPhysical_real ht x y,Complex.norm_real,Real.norm_eq_abs]
  exact WordRecursion.heatPhysical_re_bound ht le_rfl x y

/-- Strong continuity in the actual elliptic coefficient of a full
infinite physical observation row at every positive heat age. -/
theorem row {ell M T r:ℝ}(hell:0<ell)(hr:r<T)(x:HeatCircle):
    Continuous (fun f:EllipticField ell M=>NativeObservationCovariance.row hell f T r x):=by
  let v:=CircleNormalization.push.symm (circleHeat (T-r) x)
  let B:=1+heatConstant*((T-r)/2)^(-(1/2:ℝ))
  have hv:∀ᵐy:AddCircle (1:ℝ)∂haarAddCircle,‖v y‖≤B:=
    CircleNormalization.push_symm_ae_property _ (fun z:ℂ=>‖z‖≤B) (heat_bound (sub_pos.mpr hr) x)
  have hc:=BoundedHaarAnalysisContinuity.continuous_analysis ell M hell v B hv
  have hh:=realInputPart_lipschitz.continuous.comp hc
  convert! hh using 1

end SHE.NativeRowFieldContinuity
