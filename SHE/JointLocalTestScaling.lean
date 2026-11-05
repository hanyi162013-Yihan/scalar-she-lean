module

public import SHE.JointDefectScaling
public import SHE.JointInsertionBounds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace SHE.JointLocalTestScaling
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel JointWordAnalytic GaussianItoTest
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {P Ω:Type*} [MeasurableSpace P] [MeasurableSpace Ω]
variable [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable {R:ReferenceData} {n:ℕ} (L Q:Level R P n) (Λ:ℝ)
variable (U V:Ω×ℝ→CircleL2) (XU XV:Ω×(ℝ×HeatCircle)→ℝ)

/-- Literal local insertion is linear in the entire actual smooth test,
with all old observations and the newest physical V value unchanged. -/
theorem insertion_smul (w:ℝ) (p:P) (ω:Ω) (t:ℝ) (x:HeatCircle)
    (hobs:L.observations.observations p=Q.observations.observations p)
    (htime:L.terminal p=Q.terminal p) (hF:L.test p=w • Q.test p):
    insertion L Λ U V XU XV p ω t x=w*insertion Q Λ U V XU XV p ω t x:=by
  have hb:backward (L.window p) (L.test p) t=w • backward (Q.window p) (Q.test p) t:=by
    change GaussianSmooth.average (ProbabilityTheory.multivariateGaussian 0
      (covariance R.reference (L.observations.observations p)
        (ClippedCovariance.clip R.base (L.terminal p) t) (L.terminal p))) (L.test p)=_
    rw [hobs,htime,hF,NormalizedInsertion.average_smul]
    rfl
  have hs:state L Λ U V XU XV p ω t=state Q Λ U V XU XV p ω t:=by
    unfold state
    rw [hobs]
  unfold JointWordAnalytic.insertion
  rw [JointPhysicalInsertion.insertion_appendState,JointPhysicalInsertion.insertion_appendState,
    hb,NormalizedInsertion.hessian_smul,hobs,hs]
  simp only [Pi.smul_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

/-- Exact local time/space remainder scaling, before any expectation. -/
theorem remainder_smul (w:ℝ) (p:P) (ω:Ω)
    (hobs:L.observations.observations p=Q.observations.observations p)
    (htime:L.terminal p=Q.terminal p) (hF:L.test p=w • Q.test p):
    remainder L Λ U V XU XV p ω=w*remainder Q Λ U V XU XV p ω:=by
  unfold remainder
  rw [htime,←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [←integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x=>insertion_smul L Q Λ U V XU XV w p ω t x hobs htime hF)

end SHE.JointLocalTestScaling
