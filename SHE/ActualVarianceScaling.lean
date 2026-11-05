module
public import SHE.ActualVarianceLevel
public import SHE.NormalizedInsertion

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.ActualVarianceScaling
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel GaussianItoTest PhysicalIto
local instance actualVarianceScaling_period:Fact (0<2*Real.pi):=⟨by positivity⟩
variable {P Ω:Type*}[MeasurableSpace P][MeasurableSpace Ω]
variable {R:ReferenceData}{n:ℕ}(L Q:Level R P n)(a:ℝ→ℝ)
variable (U:Ω×ℝ→CircleL2)(X:Ω×(ℝ×HeatCircle)→ℝ)

/-- Linearity in the smooth test does not require regularity of the
actual coefficient multiplying its Hessian. -/
theorem inserted_smul (w:ℝ)(p:P)(ω:Ω)(t:ℝ)(x:HeatCircle)
    (hobs:L.observations.observations p=Q.observations.observations p)
    (htime:L.terminal p=Q.terminal p)(hF:L.test p=w • Q.test p):
    insertedWord (L.window p) a (fun t=>U (ω,t)) (fun q=>X (ω,q)) (L.test p) t x=
      w*insertedWord (Q.window p) a (fun t=>U (ω,t)) (fun q=>X (ω,q)) (Q.test p) t x:=by
  have hb:backward (L.window p) (L.test p) t=w • backward (Q.window p) (Q.test p) t:=by
    change GaussianSmooth.average (ProbabilityTheory.multivariateGaussian 0
      (covariance R.reference (L.observations.observations p)
        (ClippedCovariance.clip R.base (L.terminal p) t) (L.terminal p))) (L.test p)=_
    rw [hobs,htime,hF,NormalizedInsertion.average_smul]
    rfl
  unfold insertedWord
  rw [insertion_observe,insertion_observe,hb]
  dsimp only [Level.window]
  rw [hobs]
  change (1/2:ℝ)*(a (X (ω,(t,x)))-R.reference (t,x))*
      GaussianTaylor.hessian (w • backward (Q.window p) (Q.test p) t)
        (observe (fun t=>U (ω,t)) (fun q=>X (ω,q)) (Q.observations.observations p) t)
        (heatRow (Q.observations.observations p) t x) (heatRow (Q.observations.observations p) t x)=_
  rw [NormalizedInsertion.hessian_smul]
  simp only [Pi.smul_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  simp only [WordRecursion.directionalSecond,WordRecursion.hessian,GaussianTaylor.hessian,Level.window]
  ring

theorem remainder_smul (w:ℝ)(p:P)(ω:Ω)
    (hobs:L.observations.observations p=Q.observations.observations p)
    (htime:L.terminal p=Q.terminal p)(hF:L.test p=w • Q.test p):
    wordRemainder (L.window p) a (fun t=>U (ω,t)) (fun q=>X (ω,q)) (L.test p)=
      w*wordRemainder (Q.window p) a (fun t=>U (ω,t)) (fun q=>X (ω,q)) (Q.test p):=by
  unfold wordRemainder
  change (∫t in R.base..L.terminal p,_) = _
  rw [htime,←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [←integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun x=>inserted_smul L Q a U X w p ω t x hobs htime hF)

end SHE.ActualVarianceScaling
