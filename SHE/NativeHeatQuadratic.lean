module
public import SHE.NativeMultiplierTrace
public import SHE.NativeBesselHeatEnergy
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeHeatQuadratic
open Set MeasureTheory Real AddCircle StoppedFourier
open scoped NNReal ENNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩

def K (t:ℝ)(ht:0<t)(z:HeatCircle×HeatCircle):ℝ:=
  ‖NativeHeatSpan.kernel t ht z.1 z.2‖

theorem measurable_K {t:ℝ}(ht:0<t):Measurable (K t ht):=by
  have he:K t ht=fun z:HeatCircle×HeatCircle=>‖ProfileVariance.heatPhysical t z.1 z.2‖:=by
    funext z
    exact congrArg norm (NativeHeatSpan.kernel_eq_physical ht z.1 z.2)
  rw [he]
  exact (NativeHeatSpan.continuous_heatPhysical_space ht).norm.measurable

theorem K_bound {t:ℝ}(ht:0<t)(z:HeatCircle×HeatCircle):
    K t ht z≤1+heatConstant*(t/2)^(-(1/2:ℝ)):=by
  rw [K,NativeHeatSpan.kernel_norm_eq_re,NativeHeatSpan.kernel_eq_physical]
  exact (le_abs_self _).trans (WordRecursion.heatPhysical_re_bound ht le_rfl z.1 z.2)

theorem K_row {t:ℝ}(ht:0<t)(x:HeatCircle):
    (∫y:HeatCircle,K t ht (x,y) ∂haarAddCircle)=1:=
  NativeHeatSpan.kernel_norm_mass ht x

theorem K_col {t:ℝ}(ht:0<t)(y:HeatCircle):
    (∫x:HeatCircle,K t ht (x,y) ∂haarAddCircle)=1:=by
  simp only [K,NativeHeatSpan.kernel_symm ht _ y]
  exact NativeHeatSpan.kernel_norm_mass ht y

theorem half_comp {t:ℝ}(ht:0≤t)(f:CircleL2):
    circleHeatOperator (t/2) (by positivity) (circleHeatOperator (t/2) (by positivity) f)=
      circleHeatOperator t ht f:=by
  apply (fourierBasis (T:=2*Real.pi)).repr.injective
  apply lp.ext
  funext l
  simp only [fourierBasis_repr,circleHeatOperator_fourierCoeff]
  rw [←mul_assoc,←Complex.ofReal_mul,←Real.exp_add]
  congr 2
  ring

/-- Actual half-time native heat energy is a positive-kernel quadratic
form of every literal real representative. The original Haar measure
and physical time are retained exactly. -/
theorem energy {t:ℝ}(ht:0<t)(f:CircleL2)(F:HeatCircle→ℝ)
    (hf:(f:HeatCircle→ℂ)=ᵐ[haarAddCircle] fun x=>(F x:ℂ)):
    ‖circleHeatOperator (t/2) (by positivity) f‖^2=
      ∫x:HeatCircle,∫y:HeatCircle,K t ht (x,y)*F x*F y ∂haarAddCircle ∂haarAddCircle:=by
  have hh:‖circleHeatOperator (t/2) (by positivity) f‖^2=
      (inner ℂ f (circleHeatOperator t ht.le f)).re:=by
    rw [@norm_sq_eq_re_inner ℂ,circleHeatOperator_self_adjoint,half_comp ht.le f]
    rfl
  have he:inner ℂ f (circleHeatOperator t ht.le f)=
      ((∫x:HeatCircle,∫y:HeatCircle,K t ht (x,y)*F x*F y ∂haarAddCircle ∂haarAddCircle : ℝ):ℂ):=by
    rw [L2.inner_def,←_root_.integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [hf,NativeMultiplierTrace.native_heat_convolution_ae ht f] with x hx hc
    rw [hx,hc,RCLike.inner_apply,Complex.conj_ofReal,←integral_mul_const,←_root_.integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [hf] with y hy
    rw [hy]
    have hk:ProfileVariance.heatPhysical t x y=(K t ht (x,y):ℂ):=by
      rw [K,NativeHeatSpan.kernel_norm_eq_re,NativeHeatSpan.kernel_eq_physical]
      exact (WordRecursion.heatPhysical_real ht x y).symm
    rw [hk]
    push_cast
    ring
  rw [he] at hh
  exact hh

end SHE.NativeHeatQuadratic
