module

public import SHE.JointWordDefect
public import SHE.NormalizedInsertion

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.JointDefectScaling
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel
open JointWordAnalytic JointWordDefect GaussianItoTest GaussianTaylorAverage
local instance jointDefectScaling_period : Fact (0<2*Real.pi) := ⟨by positivity⟩

theorem action_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (w : ℝ)
    (H : WordRecursion.State n→L[ℝ]WordRecursion.State n→L[ℝ]ℝ) : covarianceAction A (w • H)=w*covarianceAction A H := by
  unfold covarianceAction
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

variable {P Ω : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
variable [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable {R : ReferenceData} {n : ℕ} (L Q : Level R P n) (Λ : ℝ)
variable (U V : Ω×ℝ→CircleL2) (XU XV : Ω×(ℝ×HeatCircle)→ℝ)
variable (E D : (P×Ω)×ℝ→Matrix (Fin n) (Fin n) ℝ)

/-- Exact linearity in the smooth test, with actual old joint states,
arbitrary signed matrices and all original observations retained. -/
theorem integrand_eq_of_test_smul (w : ℝ) (p : P) (ω : Ω) (t : ℝ)
    (hobs : L.observations.observations p=Q.observations.observations p)
    (htime : L.terminal p=Q.terminal p) (hF : L.test p=w • Q.test p)
    (hE : E ((p,ω),t)=D ((p,ω),t)) :
    integrand L Λ U V XU XV E ((p,ω),t)=w*integrand Q Λ U V XU XV D ((p,ω),t) := by
  have hb : backward (L.window p) (L.test p) t=w • backward (Q.window p) (Q.test p) t := by
    change GaussianSmooth.average (ProbabilityTheory.multivariateGaussian 0
      (covariance R.reference (L.observations.observations p)
        (ClippedCovariance.clip R.base (L.terminal p) t) (L.terminal p))) (L.test p)=_
    rw [hobs,htime,hF,NormalizedInsertion.average_smul]
    rfl
  have hs : state L Λ U V XU XV p ω t=state Q Λ U V XU XV p ω t := by
    unfold state
    rw [hobs]
  have hH : JointWordHessian.field L Λ U V XU XV ((p,ω),t)=
      w • JointWordHessian.field Q Λ U V XU XV ((p,ω),t) := by
    unfold JointWordHessian.field
    rw [hb,NormalizedInsertion.hessian_smul]
    simp only [Pi.smul_apply]
    rw [hs]
  rw [integrand,hE,hH,action_smul]
  unfold integrand
  ring

theorem mark_eq_of_test_smul (w : ℝ) (p : P) (ω : Ω)
    (hobs : L.observations.observations p=Q.observations.observations p)
    (htime : L.terminal p=Q.terminal p) (hF : L.test p=w • Q.test p)
    (hE : ∀ t,E ((p,ω),t)=D ((p,ω),t)) :
    mark L Λ U V XU XV E p ω=w*mark Q Λ U V XU XV D p ω := by
  unfold mark
  rw [htime,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  exact integrand_eq_of_test_smul L Q Λ U V XU XV E D w p ω t hobs htime hF (hE t)

end SHE.JointDefectScaling
