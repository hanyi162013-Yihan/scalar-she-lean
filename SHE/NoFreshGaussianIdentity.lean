module

public import SHE.NoFreshAssignedMoments
public import SHE.VectorAssignmentIdentity
public import SHE.GaussianFreshSum

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.NoFreshGaussianIdentity
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianVectorFractions
  GaussianAssignmentBlocks GaussianCoordinates GaussianConvolution
open scoped BigOperators
open Classical
variable {n d r m : ℕ}

def value (A : Fin r→Matrix (Fin n) (Fin n) ℝ) (D : Fin r→State n)
    (choices : List (Fin r×Fin (m+1))) (a : ℝ→ℝ) (F : State d→ℝ)
    (g : Fin d→Fin n) (leaf : Fin m→Fin n) (baseline : Fin m→ℝ)
    (mean : State n) (x : (Fin r→State n)×State n) : ℝ :=
  (∏j,MeasurableGaussianScores.secondScore (A j) (D j) (x.1 j))*
    VectorControlledRoot.value choices 0 F mean g x*
      ∏j,ControlledAssignedLeaf.leaf choices j.succ a mean (leaf j) (baseline j) x

theorem value_integrable (A : Fin r→Matrix (Fin n) (Fin n) ℝ) (D : Fin r→State n)
    (B : Matrix (Fin n) (Fin n) ℝ) (choices : List (Fin r×Fin (m+1)))
    (a : ℝ→ℝ) (ha : Measurable a) (F : State d→ℝ) (hF : Measurable F)
    (g : Fin d→Fin n) (leaf : Fin m→Fin n) (baseline : Fin m→ℝ) (mean : State n)
    {K M : ℝ} (hK : 0≤K) (hFb : ∀z,|F z|≤K) (hab : ∀z,|a z|≤M) :
    Integrable (value A D choices a F g leaf baseline mean)
      ((Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod (multivariateGaussian (0:State n) B)) := by
  let S:=fun x:(Fin r→State n)×State n=>∏j,MeasurableGaussianScores.secondScore (A j) (D j) (x.1 j)
  let V:=fun x:(Fin r→State n)×State n=>VectorControlledRoot.value choices 0 F mean g x*
    ∏j,ControlledAssignedLeaf.leaf choices j.succ a mean (leaf j) (baseline j) x
  have hs:Integrable S ((Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod (multivariateGaussian (0:State n) B)) :=
    (Integrable.fintype_prod (fun j=>gaussian_secondScore_integrable (A j) (D j))).comp_fst _
  have hvm:Measurable V:=(VectorControlledRoot.value_measurable choices 0 F hF mean g).mul
    (Finset.measurable_prod Finset.univ (fun j _=>ControlledAssignedLeaf.leaf_measurable choices j.succ a ha mean (leaf j) (baseline j)))
  let C:Fin (m+1)→ℝ:=Fin.cases K (fun j=>M+|baseline j|)
  have hM:0≤M:=(abs_nonneg (a 0)).trans (hab 0)
  have hC:∀j,0≤C j:=Fin.cases hK (fun j=>add_nonneg hM (abs_nonneg _))
  have hvb (x:(Fin r→State n)×State n):|V x|≤∏j,(2:ℝ)^(block choices j).length*C j := by
    rw [show V x=assignmentWord choices (VectorAssignmentIdentity.factors a F g leaf baseline mean x.2) x.1 by
      exact (VectorAssignmentIdentity.assignmentWord_eq choices a F g leaf baseline mean x.2 x.1).symm]
    apply assignmentWord_bound choices _ C hC
    refine Fin.cases (fun _=>hFb _) (fun j _=>?_)
    exact (abs_sub _ _).trans (add_le_add (hab _) le_rfl)
  convert! hs.mul_bdd hvm.aestronglyMeasurable
    (ae_of_all _ (fun x=>by simpa only [Real.norm_eq_abs] using hvb x)) using 1
  funext x
  simp only [value,S,V]
  ring

/-- Exact NO-FRESH full residual Gaussian assignment. Every original
rough factor, full baseline and old score remains in the same law. -/
theorem full_average_eq (A : Fin r→Matrix (Fin n) (Fin n) ℝ) (hA : ∀ j,(A j).PosSemidef)
    (D : Fin r→State n) (hD : ∀ j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A j)).range)
    (B : Matrix (Fin n) (Fin n) ℝ) (is : List (Fin r)) (hnd : is.Nodup)
    (a : ℝ→ℝ) (ha : Measurable a) (F : State d→ℝ) (hF : Measurable F)
    (g : Fin d→Fin n) (leaf : Fin m→Fin n) (baseline : Fin m→ℝ)
    {K M : ℝ} (hK : 0≤K) (hFb : ∀ z,|F z|≤K) (hab : ∀ z,|a z|≤M) (mean : State n) :
    gaussianAverage B (WeightedBorelAverage.average
      (Measure.pi (fun j=>multivariateGaussian (0 : State n) (A j)))
      (fun x=>∏ j,MeasurableGaussianScores.secondScore (A j) (D j) (x j)) (fun x=>∑ j,x j)
      (VectorAssignmentIdentity.raw a F g leaf baseline)) mean=
      ((assignments (m:=m+1) is).map (fun choices=>∫ x,value A D choices a F g leaf baseline mean x
        ∂(Measure.pi (fun j=>multivariateGaussian (0 : State n) (A j))).prod (multivariateGaussian (0 : State n) B))).sum := by
  let νG := (Measure.pi (fun j=>multivariateGaussian (0 : State n) (A j))).prod (multivariateGaussian (0 : State n) B)
  let cs := assignments (m:=m+1) is
  let V := fun x=>(cs.map (fun choices=>value A D choices a F g leaf baseline mean x)).sum
  have hi (choices) (_hc : choices∈cs) : Integrable (value A D choices a F g leaf baseline mean) νG :=
    value_integrable A D B choices a ha F hF g leaf baseline mean hK hFb hab
  have hV : Integrable V νG := GaussianFreshSum.integrable_sum νG cs _ hi
  have hif : Integrable (Function.uncurry (fun (old : Fin r→State n) (fresh : State n)=>V (old,fresh))) νG := by
    convert! hV using 1
  change (∫ fresh,∫ old,(∏ j,MeasurableGaussianScores.secondScore (A j) (D j) (old j))*
    VectorAssignmentIdentity.raw a F g leaf baseline (mean+fresh+∑ j,old j)
      ∂Measure.pi (fun j=>multivariateGaussian (0 : State n) (A j)) ∂multivariateGaussian 0 B)=_
  rw [←GaussianFreshSum.integral_sum νG cs _ hi,integral_prod _ hV,integral_integral_swap hif]
  apply integral_congr_ae
  apply ae_of_all
  intro fresh
  dsimp only
  rw [VectorAssignmentIdentity.old_average_eq A hA D hD is hnd a ha F hF g leaf baseline hK hFb hab mean fresh]
  apply integral_congr_ae
  apply ae_of_all
  intro old
  simp only [V,value,cs]
  simpa only [mul_assoc] using (List.sum_map_mul_left (assignments (m:=m+1) is)
    (fun choices=>VectorControlledRoot.value choices 0 F mean g (old,fresh)*
      ∏j,ControlledAssignedLeaf.leaf choices j.succ a mean (leaf j) (baseline j) (old,fresh))
    (∏j,MeasurableGaussianScores.secondScore (A j) (D j) (old j))).symm

end SHE.NoFreshGaussianIdentity
