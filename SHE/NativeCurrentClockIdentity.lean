module
public import SHE.NativeCurrentPathApplicability
public import SHE.NativeGammaVarianceShift
public import SHE.NativeCanonicalGammaFields
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeCurrentClockIdentity
open Set MeasureTheory Real NativeHeatObservation NativeMovingCurrentGamma DyadicApproximation StoppedFourier
open scoped NNReal ENNReal
local instance nativeCurrentClockIdentity_period : Fact (0<2*π):=⟨by positivity⟩
local instance nativeCurrentClockIdentity_realSigma : MeasurableSpace RealL2:=borel _
local instance nativeCurrentClockIdentity_realBorel : BorelSpace RealL2:=⟨rfl⟩
variable {Ω:Type*} [MeasurableSpace Ω]

/-- The θ=0 physical current on a covered window is the original
positive-age heat observation, with its exact absolute current clock. -/
theorem current_zero_ae (U V:ℝ≥0×Ω→RealL2) (Λ:ℝ)
    {v h τ:ℝ} (hv:0≤v) (hτ:τ∈Ioo (0:ℝ) h) (ω:Ω):
    (fun x=>PredictableScalarField.nativeField
      (NativeCorrectedCurrentFields.state U V Λ 0 v.toNNReal (v+h).toNNReal)
      (((v+h-τ).toNNReal,ω),x))=ᵐ[AddCircle.haarAddCircle]
      (fun x=>current (fun z:ℝ×Ω=>U (z.1.toNNReal,z.2)) h (τ,((v,ω),x))):=by
  have hb:0≤v+h:=by linarith [hτ.1,hτ.2]
  have hq:0≤v+h-τ:=by linarith [hτ.2]
  have he:=NativeHeatFunctionalEnergy.functional_ae hτ.1 (U ((v+h-τ).toNNReal,ω))
  refine he.mono (fun x hx=>?_)
  change PredictableScalarField.nativeField
    (fun _:Unit=>NativeCorrectedCurrentFields.state U V Λ 0 v.toNNReal (v+h).toNNReal ((v+h-τ).toNNReal,ω)) ((),x)=_
  simp only [NativeCorrectedCurrentFields.state,zero_smul,add_zero,
    Real.coe_toNNReal _ hb,Real.coe_toNNReal _ hq,
    show (v+h)-(v+h-τ)=τ by ring]
  exact hx.symm

/-- The actual held-past covariance equals the relative-clock
covariance used by the moving-current energy theorem, on the whole
covered open window. No change of profile or deterministic input occurs. -/
theorem variance_relative (P:CanonicalCovariance.ProfileParameters) (U V:ℝ≥0×Ω→RealL2)
    (Λ ξ:ℝ) (H:ℝ≥0) {v h τ:ℝ} (hv:0<v) (hvh:v+h≤H)
    (hτ:τ∈Ioo (0:ℝ) h) (ω:Ω) (x:HeatCircle):
    NativeCanonicalVarianceField.field P Λ ξ v.toNNReal (v+h).toNNReal
      (fun ω=>U (v.toNNReal,ω)) (fun ω=>V (v.toNNReal,ω)-U (v.toNNReal,ω))
      (((v+h-τ).toNNReal,ω),x)=
    variance P (fun z:ℝ×Ω=>U (z.1.toNNReal,z.2))
      (NativePathZeroExtension.extend H (fun z=>V z-U z)) Λ h ξ (τ,((v,ω),x)):=by
  have hb:0<v+h:=by linarith [hτ.1,hτ.2]
  have hq:0<v+h-τ:=by linarith [hτ.2]
  have hvq:v.toNNReal<(v+h-τ).toNNReal:=by
    exact_mod_cast (show (v.toNNReal:ℝ)<((v+h-τ).toNNReal:ℝ) by
      rw [Real.coe_toNNReal _ hv.le,Real.coe_toNNReal _ hq.le];linarith [hτ.2])
  have hqb:(v+h-τ).toNNReal≤(v+h).toNNReal:=by
    exact_mod_cast (show ((v+h-τ).toNNReal:ℝ)≤((v+h).toNNReal:ℝ) by
      rw [Real.coe_toNNReal _ hq.le,Real.coe_toNNReal _ hb.le];linarith [hτ.1])
  rw [NativeCanonicalVarianceField.field_eq P Λ ξ _ _ _ _ _ hvq hqb ω x]
  rw [NativeGammaVarianceShift.tail_relative P Λ _ _ _ ξ (by exact_mod_cast hqb)]
  have hvH:v∈Ioc (0:ℝ) (H:ℝ):=⟨hv,by linarith [hτ.1,hτ.2]⟩
  simp only [variance,ControlledScalarCovarianceTailEnergy.field,NativePathZeroExtension.extend,
    indicator_of_mem hvH,Real.coe_toNNReal _ hv.le,Real.coe_toNNReal _ hb.le,
    Real.coe_toNNReal _ hq.le,show (v+h-τ)-v=h-τ by ring,
    show (v+h)-v=h by ring,min_eq_left (by linarith [hτ.1]:h-τ≤h)]
end SHE.NativeCurrentClockIdentity
