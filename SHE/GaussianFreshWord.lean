module

public import SHE.GaussianFreshAssignments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.GaussianFreshWord
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks
  GaussianDependentScores GaussianFreshAssignments GaussianCoordinates ProfileL2
open scoped BigOperators ENNReal
variable {n d r m : ℕ}

theorem word_memLp (second : Fin r→Bool)
    (A : Fin r→Matrix (Fin n) (Fin n) ℝ) (hA : ∀ j,(A j).PosSemidef)
    (D : Fin r→State n) (hD : ∀ j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A j)).range)
    (B : Matrix (Fin n) (Fin n) ℝ) (choices : List (Fin r×Fin (m+1)))
    (a : ℝ→ℝ) (ha : Measurable a) (F : State d→ℝ) (hF : Measurable F)
    (mean : State n) (g : Fin d→Fin n) (leaf : Fin m→Fin n) (baseline : Fin m→ℝ)
    {K M : ℝ} (hK : 0≤K) (hFb : ∀ z,|F z|≤K) (hab : ∀ z,|a z|≤M) :
    MemLp (WindowFirstScoreWord.word a second A D choices F mean g leaf baseline) 2
      ((Measure.pi (fun j => multivariateGaussian (0:State n) (A j))).prod
        (multivariateGaussian (0:State n) B)) := by
  let μ := (Measure.pi (fun j => multivariateGaussian (0:State n) (A j))).prod
    (multivariateGaussian (0:State n) B)
  let S := fun x : (Fin r→State n)×State n => GaussianFractionMixedMoments.value second A D x.1
  let V := fun x : (Fin r→State n)×State n =>
    VectorControlledRoot.value choices 0 F mean g x*
      ∏ j,ControlledAssignedLeaf.leaf choices j.succ a mean (leaf j) (baseline j) x
  have hsm : Measurable S := (GaussianFractionMixedMoments.measurable_value second A D).comp measurable_fst
  have hvm : Measurable V := (VectorControlledRoot.value_measurable choices 0 F hF mean g).mul
    (Finset.measurable_prod Finset.univ (fun j _ =>
      ControlledAssignedLeaf.leaf_measurable choices j.succ a ha mean (leaf j) (baseline j)))
  have hs : MemLp S 2 μ := (memLp_two_iff_integrable_sq hsm.aestronglyMeasurable).mpr (by
    simpa only [Nat.mul_one,sq_abs] using
      (GaussianFractionMixedMoments.residual_even_moment second A hA D hD B 1).1)
  let C : Fin (m+1)→ℝ := Fin.cases K (fun j => M+|baseline j|)
  have hM : 0≤M := (abs_nonneg _).trans (hab 0)
  have hC : ∀ j,0≤C j := Fin.cases hK (fun j => add_nonneg hM (abs_nonneg _))
  have hvb (x : (Fin r→State n)×State n) :
      |V x|≤∏ j,(2:ℝ)^(block choices j).length*C j := by
    rw [show V x=assignmentWord choices
      (VectorAssignmentIdentity.factors a F g leaf baseline mean x.2) x.1 by
        exact (VectorAssignmentIdentity.assignmentWord_eq choices a F g leaf baseline mean x.2 x.1).symm]
    apply assignmentWord_bound choices _ C hC
    refine Fin.cases ?_ ?_
    · intro y
      exact hFb _
    · intro j y
      exact (abs_sub _ _).trans (add_le_add (hab _) le_rfl)
  have hv : MemLp V ∞ μ := memLp_top_of_bound hvm.aestronglyMeasurable _
    (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hvb x))
  have hw : MemLp (S*V) 2 μ := hs.mul hv
  convert! hw using 1
  funext x
  simp only [WindowFirstScoreWord.word,S,V,Pi.mul_apply]
  ring

/-- The nested terminal-first-score representation is the integral of
one actual joint Gaussian word. Both old assignments and score factors
are preserved exactly, so its norm estimate may be applied directly. -/
theorem nested_eq (T : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin r→Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (direction : State n) (D : Fin r→State n) (choices : List (Fin r×Fin (m+1)))
    (a : ℝ→ℝ) (F : State d→ℝ) (mean : State n) (g : Fin d→Fin n)
    (leaf : Fin m→Fin n) (baseline : Fin m→ℝ)
    (hi : Integrable
      (WindowFirstScoreWord.word a flags (GaussianFreshFraction.covariances T A)
        (Fin.cons direction D) (liftChoices choices) F mean g leaf baseline)
      ((Measure.pi (fun j => multivariateGaussian (0:State n)
        (GaussianFreshFraction.covariances T A j))).prod (multivariateGaussian (0:State n) B))) :
    (∫ terminal,∫ residual,(∫ old,(∏ j,MeasurableGaussianScores.secondScore (A j) (D j) (old j))*
      (VectorControlledRoot.value choices 0 F mean g (old,terminal+residual)*
        ∏ j,ControlledAssignedLeaf.leaf choices j.succ a mean (leaf j) (baseline j)
          (old,terminal+residual))
      ∂Measure.pi (fun j => multivariateGaussian (0:State n) (A j)))*
      MeasurableGaussianScores.firstScore T direction terminal
      ∂multivariateGaussian 0 B ∂multivariateGaussian 0 T)=
    ∫ x,WindowFirstScoreWord.word a flags (GaussianFreshFraction.covariances T A)
      (Fin.cons direction D) (liftChoices choices) F mean g leaf baseline x
      ∂(Measure.pi (fun j => multivariateGaussian (0:State n)
        (GaussianFreshFraction.covariances T A j))).prod (multivariateGaussian (0:State n) B) := by
  rw [GaussianFreshFraction.integral_merge_terminal_residual_old T A B _ hi]
  apply integral_congr_ae
  apply ae_of_all
  intro terminal
  apply integral_congr_ae
  apply ae_of_all
  intro residual
  dsimp only
  rw [←integral_mul_const]
  apply integral_congr_ae
  exact ae_of_all _ (fun old => (word_cons T A direction D choices a F mean g leaf baseline terminal residual old).symm)

theorem abs_nested_le_normTwo (T : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin r→Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (direction : State n) (D : Fin r→State n) (choices : List (Fin r×Fin (m+1)))
    (a : ℝ→ℝ) (F : State d→ℝ) (mean : State n) (g : Fin d→Fin n)
    (leaf : Fin m→Fin n) (baseline : Fin m→ℝ)
    (h : MemLp
      (WindowFirstScoreWord.word a flags (GaussianFreshFraction.covariances T A)
        (Fin.cons direction D) (liftChoices choices) F mean g leaf baseline) 2
      ((Measure.pi (fun j => multivariateGaussian (0:State n)
        (GaussianFreshFraction.covariances T A j))).prod (multivariateGaussian (0:State n) B))) :
    |∫ terminal,∫ residual,(∫ old,(∏ j,MeasurableGaussianScores.secondScore (A j) (D j) (old j))*
      (VectorControlledRoot.value choices 0 F mean g (old,terminal+residual)*
        ∏ j,ControlledAssignedLeaf.leaf choices j.succ a mean (leaf j) (baseline j)
          (old,terminal+residual))
      ∂Measure.pi (fun j => multivariateGaussian (0:State n) (A j)))*
      MeasurableGaussianScores.firstScore T direction terminal
      ∂multivariateGaussian 0 B ∂multivariateGaussian 0 T|≤
    normTwo ((Measure.pi (fun j => multivariateGaussian (0:State n)
      (GaussianFreshFraction.covariances T A j))).prod (multivariateGaussian (0:State n) B))
      (WindowFirstScoreWord.word a flags (GaussianFreshFraction.covariances T A)
        (Fin.cons direction D) (liftChoices choices) F mean g leaf baseline) := by
  rw [nested_eq T A B direction D choices a F mean g leaf baseline (h.integrable (by norm_num))]
  exact DependentWordAssembly.abs_integral_le_normTwo _ h

end SHE.GaussianFreshWord
