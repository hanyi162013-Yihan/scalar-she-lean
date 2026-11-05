module
public import SHE.NativeMultiplierTrace
public import SHE.NativeFourierNoiseRows
public import SHE.NativeFourierAverage
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeMultiplierFourierIntegral
open MeasureTheory AddCircle StoppedFourier
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩

theorem coefficient_apply (l:ℤ)(f:CircleL2):
    NativeFourierNoiseRows.coefficient l f=fourierCoeff f l:=by
  rw [←fourierBasis_repr]
  change inner ℂ (fourierBasis (T:=2*Real.pi) l) f=(_root_.fourierBasis (T:=2*Real.pi)).repr f l
  exact ((_root_.fourierBasis (T:=2*Real.pi)).repr_apply_apply f l).symm

/-- A literal weighted heat/Haar column has exactly the scalar spatial
Fourier input of the ORIGINAL physical row. No replacement of a square
root factor or a missing native-period multiplier occurs. -/
theorem integral (Λ ρ:ℝ)(hΛ:1≤Λ)(hρ:0≤ρ)
    (b f:CircleL2)(B:ℝ)(hb:∀ᵐx∂haarAddCircle,‖b x‖≤B)
    {t:ℝ}(ht:0<t)(l:ℤ):
    NativeFourierNoiseRows.coefficient l
      (OneInputOperator.besselHalf Λ ρ hΛ hρ
        (NativeMultiplierTrace.multiplier b B hb (circleHeatOperator t ht.le f)))=
      (((Λ+(l:ℝ)^2)^(-ρ/2):ℝ):ℂ)*
        ∫x:HeatCircle,fourier (-l) x*(b x*inner ℂ (circleHeat t x) f) ∂haarAddCircle:=by
  rw [coefficient_apply,OneInputOperator.besselHalf_fourierCoeff]
  congr 1
  unfold fourierCoeff
  apply integral_congr_ae
  filter_upwards [NativeMultiplierTrace.multiplier_ae b B hb (circleHeatOperator t ht.le f),
    heat_kernel_inner_ae ht f] with x hb hx
  simp only [smul_eq_mul,hb,←hx]
end SHE.NativeMultiplierFourierIntegral
