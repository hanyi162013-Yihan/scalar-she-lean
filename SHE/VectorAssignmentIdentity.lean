module

public import SHE.FullTerminalWord
public import SHE.VectorControlledAssignedWord
public import SHE.GaussianAssignmentSupport

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
noncomputable section

namespace SHE.VectorAssignmentIdentity
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianVectorFractions
  GaussianAssignmentBlocks GaussianCoordinates
open scoped BigOperators
variable {n d r m : ℕ}

def raw (a : ℝ→ℝ) (F : State d→ℝ) (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (baseline : Fin m→ℝ) (z : State n) : ℝ :=
  F (projection g z)*∏ j,(a (z (leaf j))-baseline j)

def factors (a : ℝ→ℝ) (F : State d→ℝ) (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (baseline : Fin m→ℝ) (mean residual : State n) : Fin (m+1)→(Fin r→State n)→ℝ :=
  Fin.cases (fun x => F (projection g (mean+residual+∑ j,x j)))
    (fun j x => a ((mean+residual+∑ j,x j) (leaf j))-baseline j)

theorem factors_product (a : ℝ→ℝ) (F : State d→ℝ) (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (baseline : Fin m→ℝ) (mean residual : State n) (x : Fin r→State n) :
    (∏ j,factors a F g leaf baseline mean residual j x)=raw a F g leaf baseline (mean+residual+∑ j,x j) := by
  simp only [factors,Fin.prod_univ_succ,Fin.cases_zero,Fin.cases_succ,raw]

/-- The canonical full-vector old assignment is exactly the root and
rough factors used by the quantitative word estimates, at the original
mean plus untouched terminal/residual Gaussian parameter. -/
theorem assignmentWord_eq (choices : List (Fin r×Fin (m+1)))
    (a : ℝ→ℝ) (F : State d→ℝ) (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (baseline : Fin m→ℝ) (mean residual : State n) (x : Fin r→State n) :
    assignmentWord choices (factors a F g leaf baseline mean residual) x=
      VectorControlledRoot.value choices 0 F mean g (x,residual)*
        ∏ j,ControlledAssignedLeaf.leaf choices j.succ a mean (leaf j) (baseline j) (x,residual) := by
  rw [assignmentWord,Fin.prod_univ_succ]
  have hroot : factors a F g leaf baseline mean residual 0=
      (fun y => F (VectorRootClips.affineSum (projection g (mean+residual))
        (fun _ : Fin r => projection g) y)) := by
    funext y
    simp only [factors,Fin.cases_zero,map_add,map_sum,VectorRootClips.affineSum]
  rw [hroot]
  apply congrArg₂ (·*·) rfl
  apply Finset.prod_congr rfl
  intro j _
  have hleaf : factors a F g leaf baseline mean residual j.succ=
      (fun y => a (GaussianRoughBlocks.affineSum (mean (leaf j)+residual (leaf j))
        (fun _ : Fin r => EuclideanSpace.proj (𝕜:=ℝ) (leaf j)) y)-baseline j) := by
    funext y
    simp only [factors,Fin.cases_succ,GaussianRoughBlocks.affineSum,EuclideanSpace.coe_proj]
    have he : (mean+residual+∑ j,y j) (leaf j)=mean (leaf j)+residual (leaf j)+∑ k,y k (leaf j) := by
      change (EuclideanSpace.proj (𝕜:=ℝ) (leaf j)) (mean+residual+∑ j,y j)=_
      rw [map_add,map_add,map_sum]
      rfl
    rw [he]
  rw [hleaf]
  rfl

theorem raw_bound (a : ℝ→ℝ) (F : State d→ℝ) (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (baseline : Fin m→ℝ) {M K : ℝ} (hK : 0≤K) (hF : ∀ z,|F z|≤K)
    (ha : ∀ z,|a z|≤M) (z : State n) :
    |raw a F g leaf baseline z|≤K*(∏ j : Fin m,(M+|baseline j|)) := by
  unfold raw
  rw [abs_mul,Finset.abs_prod]
  apply mul_le_mul (hF _) _ (Finset.prod_nonneg (fun _ _ => abs_nonneg _)) hK
  apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
  intro j _
  exact (abs_sub _ _).trans (add_le_add (ha _) le_rfl)

/-- Exact centered assignment of the literal bounded full root/rough
product under all old second scores. The untouched terminal fraction can
be substituted for `residual` before any further Gaussian integration. -/
theorem old_average_eq (A : Fin r→Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ j,(A j).PosSemidef) (D : Fin r→State n)
    (hD : ∀ j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A j)).range)
    (is : List (Fin r)) (hnd : is.Nodup) (a : ℝ→ℝ) (ha : Measurable a)
    (F : State d→ℝ) (hF : Measurable F) (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (baseline : Fin m→ℝ) {M K : ℝ} (hK : 0≤K)
    (hFb : ∀ z,|F z|≤K) (hab : ∀ z,|a z|≤M) (mean residual : State n) :
    (∫ x,(∏ j,MeasurableGaussianScores.secondScore (A j) (D j) (x j))*
      raw a F g leaf baseline (mean+residual+∑ j,x j)
      ∂Measure.pi (fun j => multivariateGaussian (0:State n) (A j)))=
    ∫ x,(∏ j,MeasurableGaussianScores.secondScore (A j) (D j) (x j))*
      ((assignments (m:=m+1) is).map (fun choices =>
        VectorControlledRoot.value choices 0 F mean g (x,residual)*
          ∏ j,ControlledAssignedLeaf.leaf choices j.succ a mean (leaf j) (baseline j) (x,residual))).sum
      ∂Measure.pi (fun j => multivariateGaussian (0:State n) (A j)) := by
  have hm : ∀ j,Measurable (factors (r:=r) a F g leaf baseline mean residual j) := by
    refine Fin.cases ?_ ?_
    · dsimp [factors]
      fun_prop
    · intro j
      dsimp [factors]
      fun_prop
  have hh := gaussian_product_identity A hA D hD is hnd (factors (r:=r) a F g leaf baseline mean residual) hm
    (K*(∏ j : Fin m,(M+|baseline j|))) (fun x => by
      rw [factors_product]
      exact raw_bound a F g leaf baseline hK hFb hab _)
  simp_rw [factors_product,assignmentWord_eq] at hh
  exact hh

end SHE.VectorAssignmentIdentity
