module
public import SHE.NativeCanonicalVarianceField
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
namespace SHE.NativeCanonicalVarianceField
open MeasureTheory StoppedFourier NativeHeatObservation DyadicApproximation
open scoped NNReal ENNReal
local instance nativeCanonicalVarianceIdentity_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeCanonicalVarianceIdentity_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩

/-- The finite Gaussian window and the native predictable variance
field are literally the same own-profile covariance on the active window. -/
theorem path_eq_field {Ω:Type*} [MeasurableSpace Ω] (P:CanonicalCovariance.ProfileParameters)
    (Λ θ:ℝ) (v b:ℝ≥0) (hvb:v≤b) (u d:Ω→RealL2)
    (q:ℝ≥0) (hvq:v<q) (hqb:q≤b) (ω:Ω) (x:HeatCircle):
    (((ControlledReferenceWindows.window P Λ θ v (ScalarCovarianceTailScale.observation b x) b
      (by exact_mod_cast hvb) (fun _=>le_rfl) (embed (u ω),embed (d ω))).path q).val 0 0)=
      field P Λ θ v b u d ((q,ω),x):=by
  rw [field_eq P Λ θ v b u d q hvq hqb ω x]
  let W:=ControlledReferenceWindows.window P Λ θ v (ScalarCovarianceTailScale.observation b x) b
    (by exact_mod_cast hvb) (fun _=>le_rfl) (embed (u ω),embed (d ω))
  have he:=W.path_eq (t:=(q:ℝ)) ⟨show (v:ℝ)≤(q:ℝ) by exact_mod_cast hvq.le,
      show (q:ℝ)≤(b:ℝ) by exact_mod_cast hqb⟩
  exact congrArg (fun A=>A 0 0) he

end SHE.NativeCanonicalVarianceField
