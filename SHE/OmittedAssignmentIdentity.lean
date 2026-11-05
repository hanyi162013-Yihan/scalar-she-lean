module

public import SHE.OmittedAssignedAverage
public import SHE.VectorAssignmentIdentity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.OmittedAssignmentIdentity
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianVectorFractions
  GaussianAssignmentBlocks GaussianCoordinates
open scoped BigOperators
open Classical
variable {n d r m : ℕ}

theorem fractionDifferences_const {E : Type*} [Zero E] (is : List (Fin r)) (c : ℝ) :
    fractionDifferences is (fun _ : Fin r→E=>c)=fun _=>if is=[] then c else 0 := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    change fractionDifference i (fractionDifferences is (fun _ : Fin r→E=>c))=_
    rw [ih]
    funext x
    simp only [fractionDifference,List.cons_ne_nil,ite_false,sub_self]

theorem replace_product (j0 : Fin m) (s : ℝ) (f : Fin m→ℝ) :
    (∏ j,if j=j0 then s else f j)=(∏ j∈Finset.univ.erase j0,f j)*s := by
  rw [←Finset.prod_erase_mul Finset.univ (fun j=>if j=j0 then s else f j) (Finset.mem_univ j0)]
  simp only [ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  exact ite_eq_right (Finset.mem_erase.mp hj).1

def raw (a : ℝ→ℝ) (F : State d→ℝ) (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (baseline : Fin m→ℝ) (j0 : Fin m) (z : State n) : ℝ :=
  F (projection g z)*∏ j∈Finset.univ.erase j0,(a (z (leaf j))-baseline j)

def factors (a : ℝ→ℝ) (F : State d→ℝ) (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (baseline : Fin m→ℝ) (j0 : Fin m) (mean residual : State n) : Fin (m+1)→(Fin r→State n)→ℝ :=
  Fin.cases (fun x=>F (projection g (mean+residual+∑ j,x j)))
    (fun j x=>if j=j0 then 1 else a ((mean+residual+∑ j,x j) (leaf j))-baseline j)

def testValue (choices : List (Fin r×Fin (m+1))) (j0 : Fin m)
    (a : ℝ→ℝ) (F : State d→ℝ) (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (baseline : Fin m→ℝ) (mean : State n) (x : (Fin r→State n)×State n) : ℝ :=
  if block choices j0.succ=[] then VectorControlledRoot.value choices 0 F mean g x*
    ∏ j∈Finset.univ.erase j0,ControlledAssignedLeaf.leaf choices j.succ a mean (leaf j) (baseline j) x else 0

theorem factors_product (a : ℝ→ℝ) (F : State d→ℝ) (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (baseline : Fin m→ℝ) (j0 : Fin m) (mean residual : State n) (x : Fin r→State n) :
    (∏ j,factors a F g leaf baseline j0 mean residual j x)=
      raw a F g leaf baseline j0 (mean+residual+∑ j,x j) := by
  simp only [factors,Fin.prod_univ_succ,Fin.cases_zero,Fin.cases_succ,OmittedAssignedMoments.omit_product,raw]

/-- A deleted baseline factor is the constant1 before old-fraction
centering. Every assignment that hits it vanishes EXACTLY; all other
original root/leaf blocks and suppressions are unchanged. -/
theorem assignmentWord_eq (choices : List (Fin r×Fin (m+1)))
    (a : ℝ→ℝ) (F : State d→ℝ) (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (baseline : Fin m→ℝ) (j0 : Fin m) (mean residual : State n) (x : Fin r→State n) :
    assignmentWord choices (factors a F g leaf baseline j0 mean residual) x=
      testValue choices j0 a F g leaf baseline mean (x,residual) := by
  rw [assignmentWord,Fin.prod_univ_succ]
  have hroot : factors a F g leaf baseline j0 mean residual 0=
      (fun y=>F (VectorRootClips.affineSum (projection g (mean+residual))
        (fun _ : Fin r=>projection g) y)) := by
    funext y
    simp only [factors,Fin.cases_zero,map_add,map_sum,VectorRootClips.affineSum]
  rw [hroot]
  have hl (j : Fin m) : fractionDifferences (block choices j.succ)
      (factors a F g leaf baseline j0 mean residual j.succ) (suppress (suppressed choices j.succ) x)=
      if j=j0 then (if block choices j0.succ=[] then 1 else 0)
      else ControlledAssignedLeaf.leaf choices j.succ a mean (leaf j) (baseline j) (x,residual) := by
    by_cases hj : j=j0
    · subst j
      simp only [factors,Fin.cases_succ,ite_true,fractionDifferences_const]
    · have hleaf : factors a F g leaf baseline j0 mean residual j.succ=
          (fun y=>a (GaussianRoughBlocks.affineSum (mean (leaf j)+residual (leaf j))
            (fun _ : Fin r=>EuclideanSpace.proj (𝕜:=ℝ) (leaf j)) y)-baseline j) := by
        funext y
        simp only [factors,Fin.cases_succ,ite_eq_right hj,GaussianRoughBlocks.affineSum,EuclideanSpace.coe_proj]
        have he : (mean+residual+∑ j,y j) (leaf j)=mean (leaf j)+residual (leaf j)+∑ k,y k (leaf j) := by
          change (EuclideanSpace.proj (𝕜:=ℝ) (leaf j)) (mean+residual+∑ j,y j)=_
          rw [map_add,map_add,map_sum]
          rfl
        rw [he]
      rw [hleaf,ite_eq_right hj]
      rfl
  simp_rw [hl]
  rw [replace_product j0]
  by_cases hb : block choices j0.succ=[]
  · simp only [testValue,ite_eq_left hb,mul_one]
    rfl
  · simp only [testValue,ite_eq_right hb,mul_zero]

theorem raw_bound (a : ℝ→ℝ) (F : State d→ℝ) (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (baseline : Fin m→ℝ) (j0 : Fin m) {K M : ℝ} (hK : 0≤K) (hF : ∀ z,|F z|≤K)
    (ha : ∀ z,|a z|≤M) (z : State n) :
    |raw a F g leaf baseline j0 z|≤K*(∏ j∈Finset.univ.erase j0,(M+|baseline j|)) := by
  unfold raw
  rw [abs_mul,Finset.abs_prod]
  apply mul_le_mul (hF _) _ (Finset.prod_nonneg (fun _ _=>abs_nonneg _)) hK
  apply Finset.prod_le_prod₀ (fun _ _=>abs_nonneg _)
  intro j _
  exact (abs_sub _ _).trans (add_le_add (ha _) le_rfl)

/-- The literal omitted original product has an exact old-score
assignment expansion. Centering is applied to the constant deleted factor
before taking absolute values, so only empty blocks survive. -/
theorem old_average_eq (A : Fin r→Matrix (Fin n) (Fin n) ℝ) (hA : ∀ j,(A j).PosSemidef)
    (D : Fin r→State n) (hD : ∀ j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A j)).range)
    (is : List (Fin r)) (hnd : is.Nodup) (a : ℝ→ℝ) (ha : Measurable a)
    (F : State d→ℝ) (hF : Measurable F) (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (baseline : Fin m→ℝ) (j0 : Fin m) {M K : ℝ} (hK : 0≤K)
    (hFb : ∀ z,|F z|≤K) (hab : ∀ z,|a z|≤M) (mean residual : State n) :
    (∫ x,(∏ j,MeasurableGaussianScores.secondScore (A j) (D j) (x j))*
      raw a F g leaf baseline j0 (mean+residual+∑ j,x j)
        ∂Measure.pi (fun j=>multivariateGaussian (0 : State n) (A j)))=
      ∫ x,(∏ j,MeasurableGaussianScores.secondScore (A j) (D j) (x j))*
        ((assignments (m:=m+1) is).map (fun choices=>testValue choices j0 a F g leaf baseline mean (x,residual))).sum
          ∂Measure.pi (fun j=>multivariateGaussian (0 : State n) (A j)) := by
  have hm : ∀ j,Measurable (factors (r:=r) a F g leaf baseline j0 mean residual j) := by
    refine Fin.cases ?_ ?_
    · dsimp only [factors,Fin.cases_zero]
      fun_prop
    · intro j
      by_cases hj : j=j0
      · simpa only [factors,Fin.cases_succ,ite_eq_left hj] using
          (measurable_const (a:=(1:ℝ)) : Measurable (fun _ : Fin r→State n=>(1:ℝ)))
      · dsimp only [factors,Fin.cases_succ]
        simp only [ite_eq_right hj]
        fun_prop
  have hh := gaussian_product_identity A hA D hD is hnd (factors (r:=r) a F g leaf baseline j0 mean residual) hm
    (K*(∏ j∈Finset.univ.erase j0,(M+|baseline j|))) (fun x=>by
      rw [factors_product]
      exact raw_bound a F g leaf baseline j0 hK hFb hab _)
  simp_rw [factors_product,assignmentWord_eq] at hh
  exact hh

end SHE.OmittedAssignmentIdentity
