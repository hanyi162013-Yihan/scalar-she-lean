module
public import SHE.InitialJointGradientEnergy
public import SHE.NativeJointRowClock
public import SHE.NativeCanonicalVarianceField
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.InitialJointGradientClock
open Set MeasureTheory Real NativeHeatObservation NativeMovingCurrentGamma DyadicApproximation StoppedFourier ScalarGaussianSemigroup PredictableL2
open scoped NNReal ENNReal
local instance : Fact (0<2*π):=⟨by positivity⟩
local instance : MeasurableSpace RealL2:=borel _
local instance : BorelSpace RealL2:=⟨rfl⟩
variable {Ω:Type*} [MeasurableSpace Ω]

def past (U V:ℝ≥0×Ω→RealL2)(ω:Ω):ControlledProfile.Inputs:=
  (embed (U (0,ω)),embed (V (0,ω)-U (0,ω)))

/-- The Borel padded variance is the actual initial own-profile
remaining covariance on the strict physical triangle. -/
theorem variance_eq (P:CanonicalCovariance.ProfileParameters)(U V:ℝ≥0×Ω→RealL2)
    (Λ h T τ:ℝ)(hT:0<T)(hT1:T≤1)(hτ:τ∈Ioo (0:ℝ) T)(ω:Ω)(x:HeatCircle):
    InitialJointGradientEnergy.variance P Λ h (past U V) (τ,(((T-h,ω),x)))=
      NativeCanonicalVarianceField.field P Λ 0 0 T.toNNReal
        (fun ω=>U (0,ω)) (fun ω=>V (0,ω)-U (0,ω)) (((T-τ).toNNReal,ω),x):=by
  have hq:0<T-τ:=sub_pos.mpr hτ.2
  have hvq:(0:ℝ≥0)<(T-τ).toNNReal:=by exact_mod_cast (show 0<((T-τ).toNNReal:ℝ) by rw [Real.coe_toNNReal _ hq.le];exact hq)
  have hqb:(T-τ).toNNReal<T.toNNReal:=by
    exact_mod_cast (show ((T-τ).toNNReal:ℝ)<(T.toNNReal:ℝ) by rw [Real.coe_toNNReal _ hq.le,Real.coe_toNNReal _ hT.le];linarith [hτ.1])
  rw [NativeCanonicalVarianceField.field_eq P Λ 0 0 T.toNNReal _ _ _ hvq hqb.le ω x]
  simp only [NNReal.coe_zero,Real.coe_toNNReal _ hq.le,Real.coe_toNNReal _ hT.le]
  have hc:=ControlledReferenceWindows.coefficient_section_measurable P Λ 0 0 (past U V ω)
  have he:=ScalarCovarianceTailScale.elliptic hc (by linarith [hτ.1]:T-τ<T)
    (by linarith [hτ.2]:T-(T-τ)≤1) P.lower_pos.le P.upper_nonneg
    (ControlledReferenceWindows.coefficient_bounds P Λ 0 0 (past U V ω)) x
  have hlo:ProfileVariance.lowerConstant*P.lower*sqrt τ≤
      ControlledScalarCovarianceTail.tail P Λ 0 (T-τ) T 0 (embed (U (0,ω))) (embed (V (0,ω)-U (0,ω))) x:=by
    convert he.1 using 1 <;> simp only [ControlledScalarCovarianceTail.tail,ControlledReferenceWindows.coefficient,
      show T-(T-τ)=τ by ring,Real.sqrt_eq_rpow,past]
    rfl
  unfold InitialJointGradientEnergy.variance
  simp only [show T-h+h=T by ring,InitialScalarCovarianceTail.field_eq P Λ 0 _ _ _ _ (by linarith [hτ.1]:T-τ≤T),past]
  exact max_eq_right hlo

def directGradient (P:CanonicalCovariance.ProfileParameters)(U V:ℝ≥0×Ω→RealL2)
    (Λ:ℝ)(H:ℝ≥0)(a:ℝ→ℝ)(j:ℕ)(h T τ:ℝ)(z:Ω×HeatCircle):ℝ:=
  let Ur:=fun p:ℝ×Ω=>U (p.1.toNNReal,p.2)
  let Dr:=NativePathZeroExtension.extend H (fun p=>V p-U p)
  let σ:=InitialJointGradientEnergy.variance P Λ h (past U V) (τ,(((T-h,z.1),z.2)))
  let x:=current Ur h (τ,(((T-h,z.1),z.2)))
  let y:=x+NativeMovingJointGamma.direction Dr Λ h (τ,(((T-h,z.1),z.2)))
  deriv (heat σ.toNNReal (ScalarHeatBands.band a (j+1))) y-
    deriv (heat σ.toNNReal (ScalarHeatBands.band a (j+1))) x

/-- Exact initial current-row gradient under the original physical
terminal/current clocks, with no frozen-law substitution. -/
theorem gradient_ae (P:CanonicalCovariance.ProfileParameters)(U V:ℝ≥0×Ω→RealL2)
    (Λ:ℝ)(H:ℝ≥0)(a:ℝ→ℝ)(j:ℕ){h T τ:ℝ}(hT:0<T)(hT1:T≤1)(hTH:T≤H)
    (hτ:τ∈Ioo (0:ℝ) T)(ω:Ω):
    let σ:=NativeCanonicalVarianceField.field P Λ 0 0 T.toNNReal
      (fun ω=>U (0,ω)) (fun ω=>V (0,ω)-U (0,ω))
    let z0:=PredictableScalarField.nativeField (NativeJointGammaCurrent.state U V Λ 0 T.toNNReal)
    let z1:=PredictableScalarField.nativeField (NativeJointGammaCurrent.state U V Λ 1 T.toNNReal)
    let q:=(T-τ).toNNReal
    (fun x=>|deriv (heat (σ ((q,ω),x)).toNNReal (ScalarHeatBands.band a (j+1))) (z0 ((q,ω),x))-
      deriv (heat (σ ((q,ω),x)).toNNReal (ScalarHeatBands.band a (j+1))) (z1 ((q,ω),x))|^2)=ᵐ[AddCircle.haarAddCircle]
      (fun x=>|directGradient P U V Λ H a j h T τ (ω,x)|^2):=by
  intro σ z0 z1 q
  have hq:0<T-τ:=sub_pos.mpr hτ.2
  have hqb:q<T.toNNReal:=by
    exact_mod_cast (show ((T-τ).toNNReal:ℝ)<(T.toNNReal:ℝ) by rw [Real.coe_toNNReal _ hq.le,Real.coe_toNNReal _ hT.le];linarith [hτ.1])
  have hqH:T-τ∈Ioc (0:ℝ) (H:ℝ):=⟨hq,by linarith [hτ.1]⟩
  filter_upwards [NativeJointGammaCurrent.scalar_ae U V Λ 0 T.toNNReal q hqb ω,
    NativeJointGammaCurrent.scalar_ae U V Λ 1 T.toNNReal q hqb ω] with x hx hy
  have hs:=variance_eq P U V Λ h T τ hT hT1 hτ ω x
  have hx':z0 ((q,ω),x)=current (fun p:ℝ×Ω=>U (p.1.toNNReal,p.2)) h (τ,(((T-h,ω),x))):=by
    simpa only [z0,q,current,Real.coe_toNNReal _ hT.le,Real.coe_toNNReal _ hq.le,
      show T-(T-τ)=τ by ring,show T-h+h-τ=T-τ by ring,zero_mul,zero_add,add_zero] using hx
  have hy':z1 ((q,ω),x)=current (fun p:ℝ×Ω=>U (p.1.toNNReal,p.2)) h (τ,(((T-h,ω),x)))+
      NativeMovingJointGamma.direction (NativePathZeroExtension.extend H (fun p=>V p-U p)) Λ h (τ,(((T-h,ω),x))):=by
    simpa only [z1,q,current,NativeMovingJointGamma.direction,NativePathZeroExtension.extend,
      show T-h+h-τ=T-τ by ring,indicator_of_mem hqH,Real.coe_toNNReal _ hT.le,Real.coe_toNNReal _ hq.le,
      show T-(T-τ)=τ by ring,one_mul] using hy
  change |deriv (heat (σ ((q,ω),x)).toNNReal (ScalarHeatBands.band a (j+1))) (z0 ((q,ω),x))-
      deriv (heat (σ ((q,ω),x)).toNNReal (ScalarHeatBands.band a (j+1))) (z1 ((q,ω),x))|^2=_
  rw [hx',hy',abs_sub_comm]
  dsimp only [directGradient]
  rw [hs]
end SHE.InitialJointGradientClock
