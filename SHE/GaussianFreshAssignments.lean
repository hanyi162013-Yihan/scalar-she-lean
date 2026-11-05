module

public import SHE.GaussianFreshFraction
public import SHE.VectorAssignmentIdentity
public import SHE.WindowFirstScoreWord

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.GaussianFreshAssignments
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianVectorFractions
  GaussianAssignmentBlocks GaussianCoordinates GaussianDependentScores
open scoped BigOperators
variable {n d r m : ℕ}

def liftChoices (choices : List (Fin r×Fin m)) : List (Fin (r+1)×Fin m) :=
  choices.map (fun p => (p.1.succ,p.2))

theorem block_lift (choices : List (Fin r×Fin m)) (k : Fin m) :
    block (liftChoices choices) k=(block choices k).map Fin.succ := by
  induction choices with
  | nil => rfl
  | cons p choices ih =>
    change block ((p.1.succ,p.2)::liftChoices choices) k=
      (block (p::choices) k).map Fin.succ
    by_cases hp : p.2=k <;> simp only [block,List.filterMap_cons,hp,ite_true,ite_false,
      List.map_cons] at *
    all_goals first | exact congrArg (fun z => p.1.succ::z) ih | exact ih

theorem suppressed_lift (choices : List (Fin r×Fin m)) (k : Fin m) :
    suppressed (liftChoices choices) k=(suppressed choices k).map Fin.succ := by
  induction choices with
  | nil => rfl
  | cons p choices ih =>
    change suppressed ((p.1.succ,p.2)::liftChoices choices) k=
      (suppressed (p::choices) k).map Fin.succ
    by_cases hp : k<p.2 <;> simp only [suppressed,List.filterMap_cons,hp,ite_true,ite_false,
      List.map_cons] at *
    all_goals first | exact congrArg (fun z => p.1.succ::z) ih | exact ih

theorem update_cons {E : Type*} [Zero E] (terminal : E) (x : Fin r→E) (i : Fin r) :
    Function.update (Fin.cons terminal x : Fin (r+1)→E) i.succ (0:E)=
      (Fin.cons terminal (Function.update x i (0:E)) : Fin (r+1)→E) := by
  classical
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · rw [Function.update_of_ne (Ne.symm (Fin.succ_ne_zero i))]
    rfl
  · by_cases hk : k=i
    · subst k;simp
    · simp [hk,Fin.succ_inj]

theorem suppress_cons {E : Type*} [Zero E] (is : List (Fin r)) (terminal : E) (x : Fin r→E) :
    suppress (is.map Fin.succ) (Fin.cons terminal x)=Fin.cons terminal (suppress is x) := by
  induction is generalizing x with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map_cons,suppress]
    rw [update_cons,ih]

theorem differences_cons {E : Type*} [Zero E] (is : List (Fin r))
    (F : (Fin (r+1)→E)→ℝ) (terminal : E) (x : Fin r→E) :
    fractionDifferences (is.map Fin.succ) F (Fin.cons terminal x)=
      fractionDifferences is (fun y => F (Fin.cons terminal y)) x := by
  induction is generalizing x with
  | nil => rfl
  | cons i is ih =>
    change fractionDifferences (is.map Fin.succ) F (Fin.cons terminal x)-
      fractionDifferences (is.map Fin.succ) F (Function.update (Fin.cons terminal x) i.succ 0)=_
    rw [update_cons,ih,ih]
    rfl

/-- Adding an untouched fresh terminal Gaussian changes neither the
old assignment nor its original root/rough factors. -/
theorem assignment_cons (choices : List (Fin r×Fin (m+1)))
    (a : ℝ→ℝ) (F : State d→ℝ) (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (baseline : Fin m→ℝ) (mean terminal residual : State n) (x : Fin r→State n) :
    assignmentWord (liftChoices choices)
      (VectorAssignmentIdentity.factors (r:=r+1) a F g leaf baseline mean residual) (Fin.cons terminal x)=
    assignmentWord choices
      (VectorAssignmentIdentity.factors (r:=r) a F g leaf baseline mean (terminal+residual)) x := by
  unfold assignmentWord
  apply Finset.prod_congr rfl
  intro k _
  rw [block_lift,suppressed_lift,suppress_cons,differences_cons]
  congr 2
  funext y
  have he : mean+residual+(∑ j,Fin.cons terminal y j)=mean+(terminal+residual)+∑ j,y j := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ]
    abel
  refine Fin.cases ?_ (fun j => ?_) k
  · simp only [VectorAssignmentIdentity.factors,Fin.cases_zero,he]
  · simp only [VectorAssignmentIdentity.factors,Fin.cases_succ,he]

/-- Exact equality of the extended fraction product with the old
canonical product evaluated at the untouched fresh terminal shift. -/
theorem root_leaf_product_cons (choices : List (Fin r×Fin (m+1)))
    (a : ℝ→ℝ) (F : State d→ℝ) (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (baseline : Fin m→ℝ) (mean terminal residual : State n) (x : Fin r→State n) :
    VectorControlledRoot.value (liftChoices choices) 0 F mean g (Fin.cons terminal x,residual)*
      (∏ j,ControlledAssignedLeaf.leaf (liftChoices choices) j.succ a mean (leaf j) (baseline j)
        (Fin.cons terminal x,residual))=
    VectorControlledRoot.value choices 0 F mean g (x,terminal+residual)*
      (∏ j,ControlledAssignedLeaf.leaf choices j.succ a mean (leaf j) (baseline j) (x,terminal+residual)) := by
  rw [←VectorAssignmentIdentity.assignmentWord_eq,←VectorAssignmentIdentity.assignmentWord_eq]
  exact assignment_cons choices a F g leaf baseline mean terminal residual x

def flags : Fin (r+1)→Bool := Fin.cases false (fun _ => true)

theorem score_product_cons (T : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin r→Matrix (Fin n) (Fin n) ℝ) (direction : State n) (D : Fin r→State n)
    (terminal : State n) (old : Fin r→State n) :
    GaussianFractionMixedMoments.value flags (GaussianFreshFraction.covariances T A)
      (Fin.cons direction D) (Fin.cons terminal old)=
      MeasurableGaussianScores.firstScore T direction terminal*
        ∏ j,MeasurableGaussianScores.secondScore (A j) (D j) (old j) := by
  simp [GaussianFractionMixedMoments.value,Fin.prod_univ_succ,flags,
    GaussianFreshFraction.covariances,Fin.cases_zero,Fin.cases_succ,Fin.cons_zero,Fin.cons_succ,
    GaussianDependentScores.factor]

/-- A fresh first-score word is exactly the old canonical assigned word
at the terminal-shifted residual. No assigned old fraction or original
root/rough block is replaced in this identity. -/
theorem word_cons (T : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin r→Matrix (Fin n) (Fin n) ℝ) (direction : State n) (D : Fin r→State n)
    (choices : List (Fin r×Fin (m+1))) (a : ℝ→ℝ) (F : State d→ℝ)
    (mean : State n) (g : Fin d→Fin n) (leaf : Fin m→Fin n) (baseline : Fin m→ℝ)
    (terminal residual : State n) (old : Fin r→State n) :
    WindowFirstScoreWord.word a flags (GaussianFreshFraction.covariances T A) (Fin.cons direction D)
      (liftChoices choices) F mean g leaf baseline (Fin.cons terminal old,residual)=
      ((∏ j,MeasurableGaussianScores.secondScore (A j) (D j) (old j))*
        (VectorControlledRoot.value choices 0 F mean g (old,terminal+residual)*
          ∏ j,ControlledAssignedLeaf.leaf choices j.succ a mean (leaf j) (baseline j)
            (old,terminal+residual)))*MeasurableGaussianScores.firstScore T direction terminal := by
  unfold WindowFirstScoreWord.word
  rw [score_product_cons]
  rw [mul_assoc,root_leaf_product_cons]
  ring

end SHE.GaussianFreshAssignments
