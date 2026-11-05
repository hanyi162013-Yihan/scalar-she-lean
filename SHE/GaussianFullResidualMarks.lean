module

public import SHE.GaussianFullResidualWord

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.GaussianFullResidualWord
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks
  GaussianDependentScores GaussianJointScoreMoments GaussianCoordinates ProfileL2
open scoped BigOperators ENNReal
variable {n d r m : ℕ}

/-- Exact finite old-assignment assembly works for both the new mean
score and the new covariance score in the full remaining Gaussian. -/
theorem sum_value_mark (second : Bool) (A : Fin r → Matrix (Fin n) (Fin n) ℝ) (D : Fin r → State n)
    (B : Matrix (Fin n) (Fin n) ℝ) (E : State n) (cs : List (List (Fin r × Fin (m+1))))
    (a : ℝ → ℝ) (F : State d → ℝ) (mean : State n) (g : Fin d → Fin n)
    (leaf : Fin m → Fin n) (baseline : Fin m → ℝ) (fresh : State n) (old : Fin r → State n) :
    (cs.map (fun choices => value second A D B E choices a F mean g leaf baseline (old,fresh))).sum=
      ((∏ j,MeasurableGaussianScores.secondScore (A j) (D j) (old j))*
        (cs.map (fun choices => VectorControlledRoot.value choices 0 F mean g (old,fresh)*
          ∏ j,ControlledAssignedLeaf.leaf choices j.succ a mean (leaf j) (baseline j) (old,fresh))).sum)*
        GaussianDependentScores.factor second B E fresh := by
  induction cs with
  | nil => simp
  | cons choices cs ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [ih]
    simp only [value,scores]
    ring

/-- The literal finite assignment sum is integrated in its original
old/fresh order. Its Fubini step follows from the full-word L2 proof. -/
theorem nested_sum_mark_eq (second : Bool) (A : Fin r → Matrix (Fin n) (Fin n) ℝ) (D : Fin r → State n)
    (B : Matrix (Fin n) (Fin n) ℝ) (E : State n) (cs : List (List (Fin r × Fin (m+1))))
    (a : ℝ → ℝ) (F : State d → ℝ) (mean : State n) (g : Fin d → Fin n)
    (leaf : Fin m → Fin n) (baseline : Fin m → ℝ)
    (hi : ∀ choices ∈ cs,Integrable (value second A D B E choices a F mean g leaf baseline)
      ((Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
        (multivariateGaussian (0 : State n) B))) :
    (∫ fresh,(∫ old,(∏ j,MeasurableGaussianScores.secondScore (A j) (D j) (old j))*
        (cs.map (fun choices => VectorControlledRoot.value choices 0 F mean g (old,fresh)*
          ∏ j,ControlledAssignedLeaf.leaf choices j.succ a mean (leaf j) (baseline j) (old,fresh))).sum
        ∂Measure.pi (fun j => multivariateGaussian (0 : State n) (A j)))*
        GaussianDependentScores.factor second B E fresh ∂multivariateGaussian 0 B)=
      (cs.map (fun choices => ∫ x,value second A D B E choices a F mean g leaf baseline x
        ∂(Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
          (multivariateGaussian (0 : State n) B))).sum := by
  let νG := (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
    (multivariateGaussian (0 : State n) B)
  let V := fun x => (cs.map (fun choices => value second A D B E choices a F mean g leaf baseline x)).sum
  have hV : Integrable V νG := GaussianFreshSum.integrable_sum νG cs _ hi
  have hif : Integrable (Function.uncurry (fun (old : Fin r → State n) (fresh : State n) => V (old,fresh))) νG := by
    convert! hV using 1
  rw [←GaussianFreshSum.integral_sum νG cs _ hi,integral_prod _ hV,integral_integral_swap hif]
  apply integral_congr_ae
  exact ae_of_all _ (fun fresh => by
    dsimp only
    rw [←integral_mul_const]
    apply integral_congr_ae
    exact ae_of_all _ (fun old => (sum_value_mark second A D B E cs a F mean g leaf baseline fresh old).symm))

end SHE.GaussianFullResidualWord
