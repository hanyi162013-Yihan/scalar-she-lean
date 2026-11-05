module
public import SHE.NativeObservationCovariance
public import SHE.PhysicalMeanRange
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.NativeObservationColumnMean
open MeasureTheory FiniteHaar StoppedFourier PhysicalMeanRange StoppedGaussianScore
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
/-- Every original common-Haar observation row coordinate is exactly
the actual physical heat mean of that SAME native Haar column. -/
theorem row {ell M T q:ℝ}(hell:0<ell)(c:EllipticField ell M)(hq:q<T)(x:HeatCircle)(k:HaarNode):
    NativeObservationCovariance.row hell c T q x k=
      PhysicalProfile.physicalHeatMean (CircleNormalization.push (globalHaarColumn k c.1)) (T-q,x):=by
  rw [PhysicalProfile.physicalHeatMean_eq (sub_pos.mpr hq)]
  change (inner ℂ (globalHaarColumn k c.1) (CircleNormalization.push.symm (circleHeat (T-q) x))).re=
    (inner ℂ (circleHeat (T-q) x) (CircleNormalization.push (globalHaarColumn k c.1))).re
  have he:=CircleNormalization.push.inner_map_map (globalHaarColumn k c.1)
    (CircleNormalization.push.symm (circleHeat (T-q) x))
  rw [LinearIsometryEquiv.apply_symm_apply] at he
  rw [←he]
  have hc:=congrArg Complex.re (inner_conj_symm (circleHeat (T-q) x) (CircleNormalization.push (globalHaarColumn k c.1)))
  simpa only [Complex.conj_re] using hc

/-- The full finite observation direction of each actual Haar input
column is precisely the native current direction used by KernelFTC. -/
theorem direction {n:ℕ}{ell M:ℝ}(hell:0<ell)(c:EllipticField ell M)
    (target:Fin n→ℝ)(center:Fin n→UnitAddCircle)(q:ℝ)(hq:∀i,q<target i)(k:HaarNode):
    WithLp.toLp 2 (fun i=>NativeObservationCovariance.row hell c (target i) q (nativeCenter center i) k)=
      currentDirection target center q (CircleNormalization.push (globalHaarColumn k c.1)):=by
  apply PiLp.ext
  intro i
  change NativeObservationCovariance.row hell c (target i) q (nativeCenter center i) k=_
  exact row hell c (hq i) (nativeCenter center i) k
end SHE.NativeObservationColumnMean
