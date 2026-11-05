module

public import SHE.OmittedAssignmentIdentity
public import SHE.GaussianFreshSum

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.OmittedAssignmentIdentity
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianVectorFractions
  GaussianAssignmentBlocks GaussianCoordinates GaussianConvolution
open scoped BigOperators
open Classical
variable {n d r m : ℕ}

def value (A : Fin r→Matrix (Fin n) (Fin n) ℝ) (D : Fin r→State n)
    (choices : List (Fin r×Fin (m+1))) (j0 : Fin m) (a : ℝ→ℝ) (F : State d→ℝ)
    (g : Fin d→Fin n) (leaf : Fin m→Fin n) (baseline : Fin m→ℝ)
    (mean : State n) (x : (Fin r→State n)×State n) : ℝ :=
  OmittedAssignedMoments.oldScores A D x*testValue choices j0 a F g leaf baseline mean x

theorem testValue_measurable (choices : List (Fin r×Fin (m+1))) (j0 : Fin m)
    (a : ℝ→ℝ) (ha : Measurable a) (F : State d→ℝ) (hF : Measurable F)
    (g : Fin d→Fin n) (leaf : Fin m→Fin n) (baseline : Fin m→ℝ) (mean : State n) :
    Measurable (testValue choices j0 a F g leaf baseline mean) := by
  change Measurable (fun x : (Fin r→State n)×State n=>if block choices j0.succ=[] then
    VectorControlledRoot.value choices 0 F mean g x*
      ∏ j∈Finset.univ.erase j0,ControlledAssignedLeaf.leaf choices j.succ a mean (leaf j) (baseline j) x else 0)
  by_cases hb : block choices j0.succ=[]
  · simp only [hb,ite_true]
    exact (VectorControlledRoot.value_measurable choices 0 F hF mean g).mul
      (Finset.measurable_prod (Finset.univ.erase j0) (fun j _=>
        ControlledAssignedLeaf.leaf_measurable choices j.succ a ha mean (leaf j) (baseline j)))
  · simp only [hb,ite_false]
    exact measurable_const

def bounds (K M : ℝ) (baseline : Fin m→ℝ) (j0 : Fin m) : Fin (m+1)→ℝ :=
  Fin.cases K (fun j=>if j=j0 then 1 else M+|baseline j|)

theorem bounds_nonneg {K M : ℝ} (hK : 0≤K) (hM : 0≤M) (baseline : Fin m→ℝ) (j0 : Fin m) :
    ∀ j,0≤bounds K M baseline j0 j := by
  refine Fin.cases hK (fun j=>?_) 
  dsimp only [bounds,Fin.cases_succ]
  split_ifs
  · positivity
  · exact add_nonneg hM (abs_nonneg _)

theorem factors_bound (a : ℝ→ℝ) (F : State d→ℝ) (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (baseline : Fin m→ℝ) (j0 : Fin m) {K M : ℝ} (hFb : ∀ z,|F z|≤K) (hab : ∀ z,|a z|≤M)
    (mean residual : State n) : ∀ j x,|factors (r:=r) a F g leaf baseline j0 mean residual j x|≤bounds K M baseline j0 j := by
  refine Fin.cases (fun x=>hFb _) (fun j x=>?_) 
  by_cases hj : j=j0
  · simp only [factors,Fin.cases_succ,ite_eq_left hj,bounds,abs_one]
    exact le_rfl
  · simp only [factors,Fin.cases_succ,ite_eq_right hj,bounds]
    exact (abs_sub _ _).trans (add_le_add (hab _) le_rfl)

theorem testValue_bound (choices : List (Fin r×Fin (m+1))) (j0 : Fin m)
    (a : ℝ→ℝ) (F : State d→ℝ) (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (baseline : Fin m→ℝ) {K M : ℝ} (hK : 0≤K) (hFb : ∀ z,|F z|≤K) (hab : ∀ z,|a z|≤M)
    (mean : State n) (x : (Fin r→State n)×State n) :
    |testValue choices j0 a F g leaf baseline mean x|≤
      ∏ j,(2:ℝ)^(block choices j).length*bounds K M baseline j0 j := by
  rw [←assignmentWord_eq choices a F g leaf baseline j0 mean x.2 x.1]
  exact assignmentWord_bound choices _ (bounds K M baseline j0)
    (bounds_nonneg hK ((abs_nonneg (a 0)).trans (hab 0)) baseline j0)
    (factors_bound a F g leaf baseline j0 hFb hab mean x.2) x.1

/-- All old/fresh Gaussian Fubini integrability is obtained from actual
old score moments and bounded original tests. -/
theorem value_integrable (A : Fin r→Matrix (Fin n) (Fin n) ℝ) (D : Fin r→State n)
    (B : Matrix (Fin n) (Fin n) ℝ) (choices : List (Fin r×Fin (m+1))) (j0 : Fin m)
    (a : ℝ→ℝ) (ha : Measurable a) (F : State d→ℝ) (hF : Measurable F)
    (g : Fin d→Fin n) (leaf : Fin m→Fin n) (baseline : Fin m→ℝ) (mean : State n)
    {K M : ℝ} (hK : 0≤K) (hFb : ∀ z,|F z|≤K) (hab : ∀ z,|a z|≤M) :
    Integrable (value A D choices j0 a F g leaf baseline mean)
      ((Measure.pi (fun j=>multivariateGaussian (0 : State n) (A j))).prod (multivariateGaussian (0 : State n) B)) := by
  have hs : Integrable (OmittedAssignedMoments.oldScores A D)
      ((Measure.pi (fun j=>multivariateGaussian (0 : State n) (A j))).prod (multivariateGaussian (0 : State n) B)) :=
    (Integrable.fintype_prod (fun j=>gaussian_secondScore_integrable (A j) (D j))).comp_fst _
  exact hs.mul_bdd (testValue_measurable choices j0 a ha F hF g leaf baseline mean).aestronglyMeasurable
    (ae_of_all _ (fun x=>by
      simpa only [Real.norm_eq_abs] using testValue_bound choices j0 a F g leaf baseline hK hFb hab mean x))

/-- Exact full residual Gaussian realization of every baseline omitted
term. The original deleted leaf survives only in its empty assignments;
all original old covariance matrices and scores remain in the same law. -/
theorem full_average_eq (A : Fin r→Matrix (Fin n) (Fin n) ℝ) (hA : ∀ j,(A j).PosSemidef)
    (D : Fin r→State n) (hD : ∀ j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A j)).range)
    (B : Matrix (Fin n) (Fin n) ℝ) (is : List (Fin r)) (hnd : is.Nodup)
    (a : ℝ→ℝ) (ha : Measurable a) (F : State d→ℝ) (hF : Measurable F)
    (g : Fin d→Fin n) (leaf : Fin m→Fin n) (baseline : Fin m→ℝ) (j0 : Fin m)
    {K M : ℝ} (hK : 0≤K) (hFb : ∀ z,|F z|≤K) (hab : ∀ z,|a z|≤M) (mean : State n) :
    gaussianAverage B (WeightedBorelAverage.average
      (Measure.pi (fun j=>multivariateGaussian (0 : State n) (A j)))
      (fun x=>∏ j,MeasurableGaussianScores.secondScore (A j) (D j) (x j)) (fun x=>∑ j,x j)
      (raw a F g leaf baseline j0)) mean=
      ((assignments (m:=m+1) is).map (fun choices=>∫ x,value A D choices j0 a F g leaf baseline mean x
        ∂(Measure.pi (fun j=>multivariateGaussian (0 : State n) (A j))).prod (multivariateGaussian (0 : State n) B))).sum := by
  let νG := (Measure.pi (fun j=>multivariateGaussian (0 : State n) (A j))).prod (multivariateGaussian (0 : State n) B)
  let cs := assignments (m:=m+1) is
  let V := fun x=>(cs.map (fun choices=>value A D choices j0 a F g leaf baseline mean x)).sum
  have hi (choices) (_hc : choices∈cs) : Integrable (value A D choices j0 a F g leaf baseline mean) νG :=
    value_integrable A D B choices j0 a ha F hF g leaf baseline mean hK hFb hab
  have hV : Integrable V νG := GaussianFreshSum.integrable_sum νG cs _ hi
  have hif : Integrable (Function.uncurry (fun (old : Fin r→State n) (fresh : State n)=>V (old,fresh))) νG := by
    convert! hV using 1
  change (∫ fresh,∫ old,(∏ j,MeasurableGaussianScores.secondScore (A j) (D j) (old j))*
    raw a F g leaf baseline j0 (mean+fresh+∑ j,old j)
      ∂Measure.pi (fun j=>multivariateGaussian (0 : State n) (A j)) ∂multivariateGaussian 0 B)=_
  rw [←GaussianFreshSum.integral_sum νG cs _ hi,integral_prod _ hV,integral_integral_swap hif]
  apply integral_congr_ae
  apply ae_of_all
  intro fresh
  dsimp only
  rw [old_average_eq A hA D hD is hnd a ha F hF g leaf baseline j0 hK hFb hab mean fresh]
  apply integral_congr_ae
  apply ae_of_all
  intro old
  simp only [V,value,OmittedAssignedMoments.oldScores,cs,List.sum_map_mul_left]

end SHE.OmittedAssignmentIdentity
