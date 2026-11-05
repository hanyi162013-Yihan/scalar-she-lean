module

public import SHE.FiniteCovariancePullback
public import SHE.FirstGammaGaussianTest

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.FiniteAffineDriftCancellation
open GaussianIncrement GaussianTaylor GaussianTaylorAverage SmoothCylinders
open FiniteCovariancePullback
open scoped ContDiff
variable {n m : ℕ}

theorem hessian_sub {F G : State m→ℝ} (hF : BoundedSmooth F) (hG : BoundedSmooth G)
    (z u v : State m) : hessian (fun w=>F w-G w) z u v=hessian F z u v-hessian G z u v := by
  have hh:=congrArg (fun T=>T ![u,v]) (iteratedFDeriv_sub_apply
    ((hF.smooth.of_le (by simp : (2:WithTop ℕ∞)≤∞)).contDiffAt (x:=z))
    ((hG.smooth.of_le (by simp : (2:WithTop ℕ∞)≤∞)).contDiffAt (x:=z)))
  have he : (fun w=>F w-G w)=F-G:=rfl
  rw [he]
  simpa only [iteratedFDeriv_two_apply,hessian,ContinuousMultilinearMap.sub_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one] using hh

theorem action_hessian_comp {C : Type*} [NormedAddCommGroup C] [InnerProductSpace ℝ C]
    (L : State m→L[ℝ]State n) (R : Fin m→C) {F : State n→ℝ} (hF : BoundedSmooth F) (z : State m) :
    covarianceAction (gram R) (hessian (fun w=>F (L w)) z)=
      covarianceAction (gram (mappedRow L R)) (hessian F (L z)) := by
  unfold covarianceAction
  simp_rw [FiniteCovariancePullback.hessian_comp L hF z]
  exact action_pullback L R (hessian F (L z))

theorem action_sub (A B : Matrix (Fin n) (Fin n) ℝ) (H : State n→L[ℝ]State n→L[ℝ]ℝ) :
    covarianceAction (A-B) H=covarianceAction A H-covarianceAction B H := by
  simp only [covarianceAction,Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]

theorem action_paired_hessian {C : Type*} [NormedAddCommGroup C] [InnerProductSpace ℝ C]
    (L M : State m→L[ℝ]State n) (R : Fin m→C) {F : State n→ℝ} (hF : BoundedSmooth F) (z : State m) :
    covarianceAction (gram R) (hessian (fun w=>F (L w)-F (M w)) z)=
      covarianceAction (gram (mappedRow L R)) (hessian F (L z))-
        covarianceAction (gram (mappedRow M R)) (hessian F (M z)) := by
  have hl : BoundedSmooth (fun w=>F (L w)):=((UniformSmooth.UniformBoundedSmooth.fixed (P:=Unit) hF).comp_right L).boundedSmooth ()
  have hm : BoundedSmooth (fun w=>F (M w)):=((UniformSmooth.UniformBoundedSmooth.fixed (P:=Unit) hF).comp_right M).boundedSmooth ()
  have he : covarianceAction (gram R) (hessian (fun w=>F (L w)-F (M w)) z)=
      covarianceAction (gram R) (hessian (fun w=>F (L w)) z)-
        covarianceAction (gram R) (hessian (fun w=>F (M w)) z) := by
    simp only [covarianceAction]
    simp_rw [hessian_sub hl hm z,mul_sub,Finset.sum_sub_distrib]
  rw [he,action_hessian_comp L R hF,action_hessian_comp M R hF]

/-- Exact mixed-pair cancellation for a time-dependent finite affine
current and a constant reference. The control derivative remains. -/
theorem cancellation {C : Type*} [NormedAddCommGroup C] [InnerProductSpace ℝ C]
    (A : Matrix (Fin n) (Fin n) ℝ) (L M DL : State m→L[ℝ]State n) (R : Fin m→C)
    {F : State n→ℝ} (hF : BoundedSmooth F) (z : State m)
    (href : gram (mappedRow M R)=A) :
    (-(1/2:ℝ)*covarianceAction A (hessian F (L z))+fderiv ℝ F (L z) (DL z))-
      (-(1/2:ℝ)*covarianceAction A (hessian F (M z)))+
      (1/2:ℝ)*covarianceAction (gram R) (hessian (fun w=>F (L w)-F (M w)) z)=
        fderiv ℝ F (L z) (DL z)+(1/2:ℝ)*covarianceAction
          (gram (mappedRow L R)-A) (hessian F (L z)) := by
  rw [action_paired_hessian L M R hF,href,action_sub]
  ring

end SHE.FiniteAffineDriftCancellation
