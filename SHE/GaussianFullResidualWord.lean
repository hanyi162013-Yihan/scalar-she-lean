module

public import SHE.GaussianFreshWord
public import SHE.FullResidualAssignedMoments
public import SHE.GaussianFreshSum

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

def value (second : Bool) (A : Fin r → Matrix (Fin n) (Fin n) ℝ) (D : Fin r → State n)
    (B : Matrix (Fin n) (Fin n) ℝ) (E : State n) (choices : List (Fin r × Fin (m+1)))
    (a : ℝ → ℝ) (F : State d → ℝ) (mean : State n) (g : Fin d → Fin n)
    (leaf : Fin m → Fin n) (baseline : Fin m → ℝ) (x : (Fin r → State n) × State n) : ℝ :=
  scores second A D B E x*VectorControlledRoot.value choices 0 F mean g x*
    ∏ j,ControlledAssignedLeaf.leaf choices j.succ a mean (leaf j) (baseline j) x

theorem value_memLp (second : Bool)
    (A : Fin r → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ j,(A j).PosSemidef)
    (D : Fin r → State n) (hD : ∀ j,D j ∈ (Matrix.toEuclideanCLM (𝕜:=ℝ) (A j)).range)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosSemidef)
    (E : State n) (hE : E ∈ (Matrix.toEuclideanCLM (𝕜:=ℝ) B).range)
    (choices : List (Fin r × Fin (m+1))) (a : ℝ → ℝ) (ha : Measurable a)
    (F : State d → ℝ) (hF : Measurable F) (mean : State n) (g : Fin d → Fin n)
    (leaf : Fin m → Fin n) (baseline : Fin m → ℝ)
    {K M : ℝ} (hK : 0 ≤ K) (hFb : ∀ z,|F z| ≤ K) (hab : ∀ z,|a z| ≤ M) :
    MemLp (value second A D B E choices a F mean g leaf baseline) 2
      ((Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
        (multivariateGaussian (0 : State n) B)) := by
  let μ := (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
    (multivariateGaussian (0 : State n) B)
  let S := scores second A D B E
  let V := fun x : (Fin r → State n) × State n =>
    VectorControlledRoot.value choices 0 F mean g x*
      ∏ j,ControlledAssignedLeaf.leaf choices j.succ a mean (leaf j) (baseline j) x
  have hsm : Measurable S := scores_measurable second A D B E
  have hvm : Measurable V := (VectorControlledRoot.value_measurable choices 0 F hF mean g).mul
    (Finset.measurable_prod Finset.univ (fun j _ =>
      ControlledAssignedLeaf.leaf_measurable choices j.succ a ha mean (leaf j) (baseline j)))
  have hs : MemLp S 2 μ := (memLp_two_iff_integrable_sq hsm.aestronglyMeasurable).mpr (by
    simpa only [Nat.mul_one,sq_abs] using (scores_even_moment second A hA D hD B hB E hE 1).1)
  let C : Fin (m+1) → ℝ := Fin.cases K (fun j => M+|baseline j|)
  have hM : 0 ≤ M := (abs_nonneg _).trans (hab 0)
  have hC : ∀ j,0 ≤ C j := Fin.cases hK (fun j => add_nonneg hM (abs_nonneg _))
  have hvb (x : (Fin r → State n) × State n) : |V x| ≤ ∏ j,(2:ℝ)^(block choices j).length*C j := by
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
  simp only [value,S,V,Pi.mul_apply]
  ring

/-- True old/fresh Gaussian Fubini for the full-residual first score.
All original assignment factors stay in the same integrand. -/
theorem nested_first_eq (A : Fin r → Matrix (Fin n) (Fin n) ℝ) (D : Fin r → State n)
    (B : Matrix (Fin n) (Fin n) ℝ) (E : State n) (choices : List (Fin r × Fin (m+1)))
    (a : ℝ → ℝ) (F : State d → ℝ) (mean : State n) (g : Fin d → Fin n)
    (leaf : Fin m → Fin n) (baseline : Fin m → ℝ)
    (hi : Integrable (value false A D B E choices a F mean g leaf baseline)
      ((Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
        (multivariateGaussian (0 : State n) B))) :
    (∫ fresh,(∫ old,(∏ j,MeasurableGaussianScores.secondScore (A j) (D j) (old j))*
        (VectorControlledRoot.value choices 0 F mean g (old,fresh)*
          ∏ j,ControlledAssignedLeaf.leaf choices j.succ a mean (leaf j) (baseline j) (old,fresh))
        ∂Measure.pi (fun j => multivariateGaussian (0 : State n) (A j)))*
        MeasurableGaussianScores.firstScore B E fresh ∂multivariateGaussian 0 B)=
      ∫ x,value false A D B E choices a F mean g leaf baseline x
        ∂(Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
          (multivariateGaussian (0 : State n) B) := by
  have hif : Integrable (Function.uncurry (fun (old : Fin r → State n) (fresh : State n) =>
      value false A D B E choices a F mean g leaf baseline (old,fresh)))
      ((Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
        (multivariateGaussian (0 : State n) B)) := by convert! hi using 1
  rw [integral_prod _ hi,integral_integral_swap hif]
  apply integral_congr_ae
  exact ae_of_all _ (fun fresh => by
    dsimp only
    rw [←integral_mul_const]
    apply integral_congr_ae
    exact ae_of_all _ (fun old => by
      simp only [value,scores,GaussianDependentScores.factor,Bool.false_eq_true,ite_false]
      ring))

theorem sum_value_first (A : Fin r → Matrix (Fin n) (Fin n) ℝ) (D : Fin r → State n)
    (B : Matrix (Fin n) (Fin n) ℝ) (E : State n) (cs : List (List (Fin r × Fin (m+1))))
    (a : ℝ → ℝ) (F : State d → ℝ) (mean : State n) (g : Fin d → Fin n)
    (leaf : Fin m → Fin n) (baseline : Fin m → ℝ) (fresh : State n) (old : Fin r → State n) :
    (cs.map (fun choices => value false A D B E choices a F mean g leaf baseline (old,fresh))).sum=
      ((∏ j,MeasurableGaussianScores.secondScore (A j) (D j) (old j))*
        (cs.map (fun choices => VectorControlledRoot.value choices 0 F mean g (old,fresh)*
          ∏ j,ControlledAssignedLeaf.leaf choices j.succ a mean (leaf j) (baseline j) (old,fresh))).sum)*
        MeasurableGaussianScores.firstScore B E fresh := by
  induction cs with
  | nil => simp
  | cons choices cs ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [ih]
    simp only [value,scores,GaussianDependentScores.factor,Bool.false_eq_true,ite_false]
    ring

/-- The literal finite assignment sum is integrated in its original
old/fresh order. Its Fubini step follows from the full-word L2 proof. -/
theorem nested_sum_first_eq (A : Fin r → Matrix (Fin n) (Fin n) ℝ) (D : Fin r → State n)
    (B : Matrix (Fin n) (Fin n) ℝ) (E : State n) (cs : List (List (Fin r × Fin (m+1))))
    (a : ℝ → ℝ) (F : State d → ℝ) (mean : State n) (g : Fin d → Fin n)
    (leaf : Fin m → Fin n) (baseline : Fin m → ℝ)
    (hi : ∀ choices ∈ cs,Integrable (value false A D B E choices a F mean g leaf baseline)
      ((Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
        (multivariateGaussian (0 : State n) B))) :
    (∫ fresh,(∫ old,(∏ j,MeasurableGaussianScores.secondScore (A j) (D j) (old j))*
        (cs.map (fun choices => VectorControlledRoot.value choices 0 F mean g (old,fresh)*
          ∏ j,ControlledAssignedLeaf.leaf choices j.succ a mean (leaf j) (baseline j) (old,fresh))).sum
        ∂Measure.pi (fun j => multivariateGaussian (0 : State n) (A j)))*
        MeasurableGaussianScores.firstScore B E fresh ∂multivariateGaussian 0 B)=
      (cs.map (fun choices => ∫ x,value false A D B E choices a F mean g leaf baseline x
        ∂(Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
          (multivariateGaussian (0 : State n) B))).sum := by
  let νG := (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
    (multivariateGaussian (0 : State n) B)
  let V := fun x => (cs.map (fun choices => value false A D B E choices a F mean g leaf baseline x)).sum
  have hV : Integrable V νG := GaussianFreshSum.integrable_sum νG cs _ hi
  have hif : Integrable (Function.uncurry (fun (old : Fin r → State n) (fresh : State n) => V (old,fresh))) νG := by
    convert! hV using 1
  rw [←GaussianFreshSum.integral_sum νG cs _ hi,integral_prod _ hV,integral_integral_swap hif]
  apply integral_congr_ae
  exact ae_of_all _ (fun fresh => by
    dsimp only
    rw [←integral_mul_const]
    apply integral_congr_ae
    exact ae_of_all _ (fun old => (sum_value_first A D B E cs a F mean g leaf baseline fresh old).symm))

end SHE.GaussianFullResidualWord
