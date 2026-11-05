module

public import SHE.NativeControlledGaussianIto
public import SHE.NativeControlledDrift
public import SHE.AffineBlockAction

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000
noncomputable section

namespace SHE.NativeControlledGenerator
open MeasureTheory GaussianIncrement GaussianConvolution GaussianTaylor GaussianTaylorAverage
open SmoothCylinders NativeHeatObservation NativeControlledGaussianFields NativeControlledGaussianIto
open DyadicApproximation
variable {n : ℕ}

def defect (W : ClippedCovariance.ObservationWindow n) (Λ θ : ℝ)
    (Γ : Matrix (Fin (n+n)) (Fin (n+n)) ℝ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  AffineBlockAction.mixed Γ (ClippedExponential.coefficient Λ θ t)-
    CovarianceMatrix.densityMatrix W.coefficient W.observations t

def vertex (W : ClippedCovariance.ObservationWindow n) (F : State n→ℝ)
    (Λ θ : ℝ) (u₀ v₀ : RealL2)
    (Γ : Matrix (Fin (n+n)) (Fin (n+n)) ℝ) (t : ℝ) (z : State (n+n)) : ℝ :=
  fderiv ℝ (gaussianAverage (W.path t).val F)
    (mean Λ θ u₀ v₀ (fun i => (W.observations i).target) (fun i => (W.observations i).center) t z)
    (NativeControlledDrift.direction Λ θ u₀ v₀ (fun i => (W.observations i).target)
      (fun i => (W.observations i).center) t z)+
  (1/2:ℝ)*covarianceAction (defect W Λ θ Γ t)
    (hessian (gaussianAverage (W.path t).val F)
      (mean Λ θ u₀ v₀ (fun i => (W.observations i).target) (fun i => (W.observations i).center) t z))

theorem covarianceAction_sub (A B : Matrix (Fin n) (Fin n) ℝ)
    (H : State n→L[ℝ]State n→L[ℝ]ℝ) :
    covarianceAction (A-B) H=covarianceAction A H-covarianceAction B H := by
  simp only [covarianceAction,Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]

theorem test_hessian_action (W : ClippedCovariance.ObservationWindow n)
    {F : State n→ℝ} (hF : BoundedSmooth F) (Λ θ : ℝ) (u₀ v₀ : RealL2)
    (Γ : Matrix (Fin (n+n)) (Fin (n+n)) ℝ) (t : ℝ) (z : State (n+n)) :
    covarianceAction Γ (hessian (test W F Λ θ u₀ v₀ t) z)=
      covarianceAction (AffineBlockAction.mixed Γ (ClippedExponential.coefficient Λ θ t))
        (hessian (gaussianAverage (W.path t).val F)
          (mean Λ θ u₀ v₀ (fun i => (W.observations i).target) (fun i => (W.observations i).center) t z)) := by
  obtain ⟨M,hM⟩ := hF.norm_bound
  obtain ⟨A,hA⟩ := hF.fderiv.norm_bound
  obtain ⟨B,hB⟩ := hF.fderiv.fderiv.norm_bound
  have hs := GaussianSmooth.contDiff_average_two (ProbabilityTheory.multivariateGaussian 0 (W.path t).val)
    (hF.smooth.of_le (by simp)) hM hA hB
  exact AffineBlockAction.covarianceAction_affine hs Γ (ClippedExponential.coefficient Λ θ t)
    (DampedAffineGaussian.shift Λ θ
      (initialDifference u₀ v₀ (fun i => (W.observations i).target) (fun i => (W.observations i).center))
      (terminalShift Λ θ u₀ v₀ (fun i => (W.observations i).target) (fun i => (W.observations i).center)) t) z

/-- The backward physical covariance cancels exactly. What remains is
the genuine controlled drift and the full mixed noise covariance defect,
including both ordered cross pairs. -/
theorem generator_eq_vertex (W : ClippedCovariance.ObservationWindow n)
    {F : State n→ℝ} (hF : BoundedSmooth F) (Λ θ : ℝ) (u₀ v₀ : RealL2)
    (Γ : Matrix (Fin (n+n)) (Fin (n+n)) ℝ) (t : ℝ) (z : State (n+n)) :
    testDerivative W F Λ θ u₀ v₀ t z+
        (1/2:ℝ)*covarianceAction Γ (hessian (test W F Λ θ u₀ v₀ t) z)=
      vertex W F Λ θ u₀ v₀ Γ t z := by
  rw [test_hessian_action W hF Λ θ u₀ v₀ Γ t z]
  unfold testDerivative GaussianAffineFields.derivative vertex defect
  rw [covarianceAction_sub]
  dsimp only [mean,NativeControlledDrift.direction]
  change -(1/2:ℝ)*_+_+(1/2:ℝ)*_=_+(1/2:ℝ)*(_-_)
  ring

end SHE.NativeControlledGenerator
