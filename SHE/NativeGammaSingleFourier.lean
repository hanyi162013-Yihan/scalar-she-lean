module
public import SHE.NativeMultiplierFourierIntegral
public import SHE.NativePairedColumnFields
public import SHE.NativeHeatRowsForward
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SHE.NativeGammaSingleFourier
open Set MeasureTheory AddCircle StoppedFourier FiniteHaar
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
variable {P:Type*}[MeasurableSpace P]
variable {Λ ρ m U:ℝ}(hΛ:1≤Λ)(hρ:0≤ρ)(hρhalf:ρ<1/2)(hm:0<m)
variable (B:ℝ)(g:Fin 6→P×HeatCircle→ℂ)(hgm:∀i,Measurable (g i))
variable (hg:∀i p x,‖g i (p,x)‖≤B)
variable (t:P→ℝ)(htm:Measurable t)(ht:∀p,0<t p)(ht1:∀p,t p≤1)

/-- Each of the actual six weighted Hilbert columns has EXACTLY the
spatial Fourier average of its original common-Haar scalar row. -/
theorem coefficient (i:Fin 6)(c:P→EllipticField m U)(p:P)(k:HaarNode)(l:ℤ):
    NativeFourierNoiseRows.coefficient l
      (NativePairedColumnFields.single hΛ hρ hρhalf hm B g hgm hg t htm ht ht1 i c p k)=
      (((Λ+(l:ℝ)^2)^(-ρ/2):ℝ):ℂ)*
        ∫x:HeatCircle,fourier (-l) x*
          (g i (p,x)*(NativeObservationCovariance.row hm (c p) (t p) 0 x k:ℂ)) ∂haarAddCircle:=by
  change NativeFourierNoiseRows.coefficient l
    (NativeMultiplierColumnFields.column hΛ hρ (g i) t hm c p k)=_
  rw [NativeMultiplierColumnFields.column,
    NativeMultiplierColumnFields.operator_eq (hgm i) (fun _=>B) (hg i) htm ht,
    NativeMultiplierFourierIntegral.coefficient_apply,OneInputOperator.besselHalf_fourierCoeff]
  congr 1
  unfold fourierCoeff
  apply integral_congr_ae
  have he:=NativeHeatRowsForward.multiplier_row_ae (T:=t p) (q:=0) hm (c p) (ht p)
    (hgm i) (fun _=>B) (hg i) p k
  simp only [sub_zero] at he
  filter_upwards [he] with x hx
  simp only [smul_eq_mul,hx]
end SHE.NativeGammaSingleFourier
