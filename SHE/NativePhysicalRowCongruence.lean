module
public import SHE.NativePhysicalRowFields
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.NativeObservationCovariance
open FiniteHaar StoppedFourier
local instance nativePhysicalRowCongruence_period : Fact (0<2*Real.pi):=⟨by positivity⟩

/-- Physical Haar analysis rows depend on the actual coefficient,
not on which certified ellipticity interval is used to package it. -/
theorem row_congr {ell M m U:ℝ} (hell:0<ell) (hm:0<m)
    (f:EllipticField ell M) (g:EllipticField m U) (hfg:f.1=g.1)
    (T r:ℝ) (x:HeatCircle):row hell f T r x=row hm g T r x:=by
  apply lp.ext
  funext q
  change (inner ℂ (globalHaarColumn q f.1)
    (CircleNormalization.push.symm (circleHeat (T-r) x))).re=
    (inner ℂ (globalHaarColumn q g.1)
    (CircleNormalization.push.symm (circleHeat (T-r) x))).re
  rw [hfg]

end SHE.NativeObservationCovariance
