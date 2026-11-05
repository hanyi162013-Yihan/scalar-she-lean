module

public import SHE.GaussianFullResidualWord

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SHE.GaussianOldFreshWord
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianAssignmentBlocks
  GaussianVectorFractions MeasurableGaussianScores
open scoped BigOperators
variable {Y:Type*} [MeasurableSpace Y] {n d r m:ℕ}

/-- Only old fractions are assigned to root and rough blocks. The
fresh parameter and its complete score weight remain untouched. -/
def value (A:Fin r→MeasurableGeneralizedInverse.Mat n) (D:Fin r→State n)
    (T:Y→ℝ) (residual:Y→State n) (choices:List (Fin r×Fin (m+1)))
    (a:ℝ→ℝ) (F:State d→ℝ) (mean:State n) (g:Fin d→Fin n)
    (leaf:Fin m→Fin n) (baseline:Fin m→ℝ) (z:(Fin r→State n)×Y):ℝ:=
  ((∏j,secondScore (A j) (D j) (z.1 j))*T z.2)*
    (VectorControlledRoot.value choices 0 F mean g (z.1,residual z.2)*
      ∏j,ControlledAssignedLeaf.leaf choices j.succ a mean (leaf j) (baseline j) (z.1,residual z.2))

theorem value_integrable (ν:Measure Y) [SFinite ν]
    (A:Fin r→MeasurableGeneralizedInverse.Mat n) (D:Fin r→State n)
    (T:Y→ℝ) (hT:Integrable T ν) (residual:Y→State n) (hr:Measurable residual)
    (choices:List (Fin r×Fin (m+1))) (a:ℝ→ℝ) (ha:Measurable a)
    (F:State d→ℝ) (hF:Measurable F) (mean:State n) (g:Fin d→Fin n)
    (leaf:Fin m→Fin n) (baseline:Fin m→ℝ)
    {K M:ℝ} (hK:0≤K) (hFb:∀z,|F z|≤K) (hab:∀z,|a z|≤M):
    Integrable (value A D T residual choices a F mean g leaf baseline)
      ((Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod ν):=by
  let V:=fun z:(Fin r→State n)×Y=>VectorControlledRoot.value choices 0 F mean g (z.1,residual z.2)*
    ∏j,ControlledAssignedLeaf.leaf choices j.succ a mean (leaf j) (baseline j) (z.1,residual z.2)
  have hp:Measurable (fun z:(Fin r→State n)×Y=>(z.1,residual z.2)):=
    measurable_fst.prodMk (hr.comp measurable_snd)
  have hVm:Measurable V:=((VectorControlledRoot.value_measurable choices 0 F hF mean g).mul
    (Finset.measurable_prod Finset.univ (fun j _=>
      ControlledAssignedLeaf.leaf_measurable choices j.succ a ha mean (leaf j) (baseline j)))).comp hp
  let C:Fin (m+1)→ℝ:=Fin.cases K (fun j=>M+|baseline j|)
  have hM:0≤M:=(abs_nonneg _).trans (hab 0)
  have hC:∀j,0≤C j:=Fin.cases hK (fun j=>add_nonneg hM (abs_nonneg _))
  have hVb(z:(Fin r→State n)×Y):|V z|≤∏j,(2:ℝ)^(block choices j).length*C j:=by
    rw [show V z=assignmentWord choices
      (VectorAssignmentIdentity.factors a F g leaf baseline mean (residual z.2)) z.1 by
        exact (VectorAssignmentIdentity.assignmentWord_eq choices a F g leaf baseline mean (residual z.2) z.1).symm]
    apply assignmentWord_bound choices _ C hC
    refine Fin.cases ?_ ?_
    · intro x
      exact hFb _
    · intro j x
      exact (abs_sub _ _).trans (add_le_add (hab _) le_rfl)
  have hs:=Integrable.fintype_prod (fun j=>gaussian_secondScore_integrable (A j) (D j))
  exact (hs.mul_prod hT).mul_bdd hVm.aestronglyMeasurable
    (ae_of_all _ (fun z=>by simpa only [Real.norm_eq_abs] using hVb z))

theorem sum_value (A:Fin r→MeasurableGeneralizedInverse.Mat n) (D:Fin r→State n)
    (T:Y→ℝ) (residual:Y→State n) (cs:List (List (Fin r×Fin (m+1))))
    (a:ℝ→ℝ) (F:State d→ℝ) (mean:State n) (g:Fin d→Fin n)
    (leaf:Fin m→Fin n) (baseline:Fin m→ℝ) (old:Fin r→State n) (y:Y):
    (cs.map (fun choices=>value A D T residual choices a F mean g leaf baseline (old,y))).sum=
      ((∏j,secondScore (A j) (D j) (old j))*
        (cs.map (fun choices=>VectorControlledRoot.value choices 0 F mean g (old,residual y)*
          ∏j,ControlledAssignedLeaf.leaf choices j.succ a mean (leaf j) (baseline j) (old,residual y))).sum)*T y:=by
  induction cs with
  | nil=>simp
  | cons choices cs ih=>
    simp only [List.map_cons,List.sum_cons]
    rw [ih]
    simp only [value]
    ring

/-- Genuine old/fresh Fubini and exact old-score assignment. All
integrability is derived from bounded root/leaves and the actual fresh
weight; no moment or Fubini assumption is added to the representation. -/
theorem assignment_integral (ν:Measure Y) [SFinite ν]
    (A:Fin r→MeasurableGeneralizedInverse.Mat n) (hA:∀j,(A j).PosSemidef)
    (D:Fin r→State n) (hD:∀j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A j)).range)
    (T:Y→ℝ) (hT:Integrable T ν) (residual:Y→State n) (hr:Measurable residual)
    (is:List (Fin r)) (hnd:is.Nodup) (a:ℝ→ℝ) (ha:Measurable a)
    (F:State d→ℝ) (hF:Measurable F) (mean:State n) (g:Fin d→Fin n)
    (leaf:Fin m→Fin n) (baseline:Fin m→ℝ)
    {K M:ℝ} (hK:0≤K) (hFb:∀z,|F z|≤K) (hab:∀z,|a z|≤M):
    (∫y,(∫old,(∏j,secondScore (A j) (D j) (old j))*
        VectorAssignmentIdentity.raw a F g leaf baseline (mean+residual y+∑j,old j)
        ∂Measure.pi (fun j=>multivariateGaussian (0:State n) (A j)))*T y ∂ν)=
      ((assignments (m:=m+1) is).map (fun choices=>∫z,
        value A D T residual choices a F mean g leaf baseline z
        ∂(Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod ν)).sum:=by
  let cs:=assignments (m:=m+1) is
  let μ:=(Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod ν
  have hi(choices):Integrable (value A D T residual choices a F mean g leaf baseline) μ:=
    value_integrable ν A D T hT residual hr choices a ha F hF mean g leaf baseline hK hFb hab
  let V:=fun z=>(cs.map (fun choices=>value A D T residual choices a F mean g leaf baseline z)).sum
  have hV:Integrable V μ:=GaussianFreshSum.integrable_sum μ cs _ (fun choices _=>hi choices)
  have hif:Integrable (Function.uncurry (fun (old:Fin r→State n) (y:Y)=>V (old,y))) μ:=by
    convert! hV using 1
  rw [←GaussianFreshSum.integral_sum μ cs _ (fun choices _=>hi choices),integral_prod _ hV,
    integral_integral_swap hif]
  apply integral_congr_ae
  exact ae_of_all _ (fun y=>by
    dsimp only
    rw [VectorAssignmentIdentity.old_average_eq A hA D hD is hnd a ha F hF g leaf baseline hK hFb hab mean (residual y)]
    rw [←integral_mul_const]
    apply integral_congr_ae
    exact ae_of_all _ (fun old=>(sum_value A D T residual cs a F mean g leaf baseline old y).symm))

end SHE.GaussianOldFreshWord
