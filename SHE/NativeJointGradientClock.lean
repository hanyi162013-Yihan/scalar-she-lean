module
public import SHE.NativeCurrentClockIdentity
public import SHE.NativeJointGammaCurrent
public import SHE.NativeMovingJointGamma
public import SHE.ScalarHeatSixNorms
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeJointGradientClock
open Set MeasureTheory Real NativeHeatObservation NativeMovingCurrentGamma DyadicApproximation StoppedFourier ScalarGaussianSemigroup
open scoped NNReal ENNReal
local instance nativeJointGradientClock_period : Fact (0<2*π):=⟨by positivity⟩
local instance nativeJointGradientClock_realSigma : MeasurableSpace RealL2:=borel _
local instance nativeJointGradientClock_realBorel : BorelSpace RealL2:=⟨rfl⟩
variable {Ω:Type*} [MeasurableSpace Ω]

/-- Exact current-gradient integrand under the original absolute
clock and the jointly Borel moving-current representation. Only an
AE spatial representative equality is used; the laws remain unchanged. -/
theorem gradient_ae (P:CanonicalCovariance.ProfileParameters) (U V:ℝ≥0×Ω→RealL2)
    (Λ:ℝ) (H:ℝ≥0) (a:ℝ→ℝ) (j:ℕ) {v h τ:ℝ} (hv:0<v) (hvh:v+h≤H)
    (hτ:τ∈Ioo (0:ℝ) h) (ω:Ω):
    let σ:=NativeCanonicalVarianceField.field P Λ 0 v.toNNReal (v+h).toNNReal
      (fun ω=>U (v.toNNReal,ω)) (fun ω=>V (v.toNNReal,ω)-U (v.toNNReal,ω))
    let z0:=PredictableScalarField.nativeField (NativeJointGammaCurrent.state U V Λ 0 (v+h).toNNReal)
    let z1:=PredictableScalarField.nativeField (NativeJointGammaCurrent.state U V Λ 1 (v+h).toNNReal)
    let q:=(v+h-τ).toNNReal
    let Ureal:=fun z:ℝ×Ω=>U (z.1.toNNReal,z.2)
    let Dreal:=NativePathZeroExtension.extend H (fun z=>V z-U z)
    (fun x=>|deriv (heat (σ ((q,ω),x)).toNNReal (ScalarHeatBands.band a (j+1))) (z0 ((q,ω),x))-
      deriv (heat (σ ((q,ω),x)).toNNReal (ScalarHeatBands.band a (j+1))) (z1 ((q,ω),x))|^2)=ᵐ[AddCircle.haarAddCircle]
    (fun x=>|deriv (heat (variance P Ureal Dreal Λ h 0 (τ,((v,ω),x))).toNNReal (ScalarHeatBands.band a (j+1)))
        (current Ureal h (τ,((v,ω),x))+NativeMovingJointGamma.direction Dreal Λ h (τ,((v,ω),x)))-
      deriv (heat (variance P Ureal Dreal Λ h 0 (τ,((v,ω),x))).toNNReal (ScalarHeatBands.band a (j+1)))
        (current Ureal h (τ,((v,ω),x)))|^2):=by
  intro σ z0 z1 q Ureal Dreal
  have hb:0<v+h:=by linarith [hτ.1,hτ.2]
  have hq:0<v+h-τ:=by linarith [hτ.2]
  have hqb:q<(v+h).toNNReal:=by
    exact_mod_cast (show ((v+h-τ).toNNReal:ℝ)<((v+h).toNNReal:ℝ) by
      rw [Real.coe_toNNReal _ hq.le,Real.coe_toNNReal _ hb.le];linarith [hτ.1])
  have hqH:v+h-τ∈Ioc (0:ℝ) (H:ℝ):=⟨hq,by linarith [hτ.1]⟩
  filter_upwards [NativeJointGammaCurrent.scalar_ae U V Λ 0 (v+h).toNNReal q hqb ω,
    NativeJointGammaCurrent.scalar_ae U V Λ 1 (v+h).toNNReal q hqb ω] with x hx hy
  have hs:=NativeCurrentClockIdentity.variance_relative P U V Λ 0 H hv hvh hτ ω x
  change σ ((q,ω),x)=variance P Ureal Dreal Λ h 0 (τ,((v,ω),x)) at hs
  have hx':z0 ((q,ω),x)=current Ureal h (τ,((v,ω),x)):=by
    simpa only [z0,q,current,Real.coe_toNNReal _ hb.le,Real.coe_toNNReal _ hq.le,
      show (v+h)-(v+h-τ)=τ by ring,zero_mul,zero_add,add_zero] using hx
  have hy':z1 ((q,ω),x)=current Ureal h (τ,((v,ω),x))+
      NativeMovingJointGamma.direction Dreal Λ h (τ,((v,ω),x)):=by
    simpa only [z1,q,current,NativeMovingJointGamma.direction,Dreal,NativePathZeroExtension.extend,
      indicator_of_mem hqH,Real.coe_toNNReal _ hb.le,Real.coe_toNNReal _ hq.le,
      show (v+h)-(v+h-τ)=τ by ring,one_mul] using hy
  rw [hs,hx',hy',abs_sub_comm]

/-- Equality of the actual spatial current-slot energy, for every
covered original past/current and every sample. This is the literal
normalization consumed by the complete Gamma bound. -/
theorem spatial_integral (P:CanonicalCovariance.ProfileParameters) (U V:ℝ≥0×Ω→RealL2)
    (Λ:ℝ) (H:ℝ≥0) (a:ℝ→ℝ) (j:ℕ) {v h τ:ℝ} (hv:0<v) (hvh:v+h≤H)
    (hτ:τ∈Ioo (0:ℝ) h) (ω:Ω):
    let σ:=NativeCanonicalVarianceField.field P Λ 0 v.toNNReal (v+h).toNNReal
      (fun ω=>U (v.toNNReal,ω)) (fun ω=>V (v.toNNReal,ω)-U (v.toNNReal,ω))
    let z0:=PredictableScalarField.nativeField (NativeJointGammaCurrent.state U V Λ 0 (v+h).toNNReal)
    let z1:=PredictableScalarField.nativeField (NativeJointGammaCurrent.state U V Λ 1 (v+h).toNNReal)
    let q:=(v+h-τ).toNNReal
    let Ureal:=fun z:ℝ×Ω=>U (z.1.toNNReal,z.2)
    let Dreal:=NativePathZeroExtension.extend H (fun z=>V z-U z)
    (∫x,|deriv (heat (σ ((q,ω),x)).toNNReal (ScalarHeatBands.band a (j+1))) (z0 ((q,ω),x))-
      deriv (heat (σ ((q,ω),x)).toNNReal (ScalarHeatBands.band a (j+1))) (z1 ((q,ω),x))|^2 ∂AddCircle.haarAddCircle)=
    ∫x,|deriv (heat (variance P Ureal Dreal Λ h 0 (τ,((v,ω),x))).toNNReal (ScalarHeatBands.band a (j+1)))
        (current Ureal h (τ,((v,ω),x))+NativeMovingJointGamma.direction Dreal Λ h (τ,((v,ω),x)))-
      deriv (heat (variance P Ureal Dreal Λ h 0 (τ,((v,ω),x))).toNNReal (ScalarHeatBands.band a (j+1)))
        (current Ureal h (τ,((v,ω),x)))|^2 ∂AddCircle.haarAddCircle:=by
  exact integral_congr_ae (gradient_ae P U V Λ H a j hv hvh hτ ω)
end SHE.NativeJointGradientClock
