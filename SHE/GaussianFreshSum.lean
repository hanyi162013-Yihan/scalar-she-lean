module

public import SHE.GaussianFreshWord

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.GaussianFreshSum
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks
  GaussianDependentScores GaussianFreshAssignments GaussianCoordinates ProfileL2
open scoped BigOperators
variable {n d r m : ℕ}

theorem integrable_sum {ι Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (is : List ι) (f : ι→Ω→ℝ) (hf : ∀ i∈is,Integrable (f i) μ) :
    Integrable (fun x => (is.map (fun i => f i x)).sum) μ := by
  induction is with
  | nil => convert! integrable_zero Ω ℝ μ using 1
  | cons i is ih =>
    convert! (hf i (by simp)).add (ih (fun j hj => hf j (by simp [hj]))) using 1

theorem integral_sum {ι Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (is : List ι) (f : ι→Ω→ℝ) (hf : ∀ i∈is,Integrable (f i) μ) :
    (∫ x,(is.map (fun i => f i x)).sum ∂μ)=(is.map (fun i => ∫ x,f i x ∂μ)).sum := by
  induction is with
  | nil => simp
  | cons i is ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [integral_add (hf i (by simp)) (integrable_sum μ is f (fun j hj => hf j (by simp [hj]))),
      ih (fun j hj => hf j (by simp [hj]))]

theorem abs_sum_le {ι : Type*} (is : List ι) (f g : ι→ℝ)
    (hfg : ∀ i∈is,|f i|≤g i) : |(is.map f).sum|≤(is.map g).sum := by
  induction is with
  | nil => simp
  | cons i is ih =>
    simp only [List.map_cons,List.sum_cons]
    exact (abs_add_le _ _).trans (add_le_add (hfg i (by simp)) (ih (fun j hj => hfg j (by simp [hj]))))

theorem sum_word_cons (T : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin r→Matrix (Fin n) (Fin n) ℝ) (direction : State n) (D : Fin r→State n)
    (cs : List (List (Fin r×Fin (m+1)))) (a : ℝ→ℝ) (F : State d→ℝ)
    (mean : State n) (g : Fin d→Fin n) (leaf : Fin m→Fin n) (baseline : Fin m→ℝ)
    (terminal residual : State n) (old : Fin r→State n) :
    (cs.map (fun choices => WindowFirstScoreWord.word a flags (GaussianFreshFraction.covariances T A)
      (Fin.cons direction D) (liftChoices choices) F mean g leaf baseline (Fin.cons terminal old,residual))).sum=
    ((∏ j,MeasurableGaussianScores.secondScore (A j) (D j) (old j))*
      (cs.map (fun choices => VectorControlledRoot.value choices 0 F mean g (old,terminal+residual)*
        ∏ j,ControlledAssignedLeaf.leaf choices j.succ a mean (leaf j) (baseline j)
          (old,terminal+residual))).sum)*MeasurableGaussianScores.firstScore T direction terminal := by
  induction cs with
  | nil => simp
  | cons choices cs ih =>
    rw [List.map_cons,List.sum_cons,List.map_cons,List.sum_cons,word_cons,ih]
    ring

/-- The whole finite assignment sum in the literal terminal
representation equals a single joint Gaussian integral of the actual
first/second-score assigned words. All Fubini integrability follows from
the individual actual word integrability. -/
theorem nested_sum_eq (T : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin r→Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (direction : State n) (D : Fin r→State n) (cs : List (List (Fin r×Fin (m+1))))
    (a : ℝ→ℝ) (F : State d→ℝ) (mean : State n) (g : Fin d→Fin n)
    (leaf : Fin m→Fin n) (baseline : Fin m→ℝ)
    (hi : ∀ choices∈cs,Integrable
      (WindowFirstScoreWord.word a flags (GaussianFreshFraction.covariances T A)
        (Fin.cons direction D) (liftChoices choices) F mean g leaf baseline)
      ((Measure.pi (fun j => multivariateGaussian (0:State n)
        (GaussianFreshFraction.covariances T A j))).prod (multivariateGaussian (0:State n) B))) :
    (∫ terminal,∫ residual,(∫ old,(∏ j,MeasurableGaussianScores.secondScore (A j) (D j) (old j))*
      (cs.map (fun choices => VectorControlledRoot.value choices 0 F mean g (old,terminal+residual)*
        ∏ j,ControlledAssignedLeaf.leaf choices j.succ a mean (leaf j) (baseline j)
          (old,terminal+residual))).sum
      ∂Measure.pi (fun j => multivariateGaussian (0:State n) (A j)))*
      MeasurableGaussianScores.firstScore T direction terminal
      ∂multivariateGaussian 0 B ∂multivariateGaussian 0 T)=
    (cs.map (fun choices => ∫ x,WindowFirstScoreWord.word a flags (GaussianFreshFraction.covariances T A)
      (Fin.cons direction D) (liftChoices choices) F mean g leaf baseline x
      ∂(Measure.pi (fun j => multivariateGaussian (0:State n)
        (GaussianFreshFraction.covariances T A j))).prod (multivariateGaussian (0:State n) B))).sum := by
  rw [←integral_sum _ cs _ hi]
  rw [GaussianFreshFraction.integral_merge_terminal_residual_old T A B _ (integrable_sum _ cs _ hi)]
  apply integral_congr_ae
  apply ae_of_all
  intro terminal
  apply integral_congr_ae
  apply ae_of_all
  intro residual
  dsimp only
  rw [←integral_mul_const]
  apply integral_congr_ae
  exact ae_of_all _ (fun old => (sum_word_cons T A direction D cs a F mean g leaf baseline terminal residual old).symm)

end SHE.GaussianFreshSum
