module

public import SHE.NativeFirstOmittedFields
public import SHE.TwoFreshAverageOrder
public import SHE.OmittedFullAverage

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
namespace SHE.NativeFirstOmittedAssignment
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianAssignmentBlocks
  GaussianVectorFractions MeasurableGaussianScores
open scoped BigOperators
variable {n d r m:ℕ}

def value (A:Fin r→MeasurableGeneralizedInverse.Mat n) (D:Fin r→State n)
    (R:MeasurableGeneralizedInverse.Mat n) (E:State n)
    (choices:List (Fin r×Fin (m+1))) (j0:Fin m) (a:ℝ→ℝ) (F:State d→ℝ)
    (mean:State n) (g:Fin d→Fin n) (leaf:Fin m→Fin n) (baseline:Fin m→ℝ)
    (z:(Fin r→State n)×(State n×State n)):ℝ:=
  NativeFirstOldScoreMoments.scores A D R E z*
    OmittedAssignmentIdentity.testValue choices j0 a F g leaf baseline mean (z.1,z.2.1+z.2.2)

theorem value_eq (A:Fin r→MeasurableGeneralizedInverse.Mat n) (D:Fin r→State n)
    (R:MeasurableGeneralizedInverse.Mat n) (E:State n)
    (choices:List (Fin r×Fin (m+1))) (j0:Fin m) (a:ℝ→ℝ) (F:State d→ℝ)
    (mean:State n) (g:Fin d→Fin n) (leaf:Fin m→Fin n) (baseline:Fin m→ℝ)
    (z:(Fin r→State n)×(State n×State n)):
    value A D R E choices j0 a F mean g leaf baseline z=
      if block choices j0.succ=[] then NativeFirstOmittedMoments.word A D R E choices j0
        a F (fun _:Unit=>mean) g leaf baseline ((),z) else 0:=by
  by_cases hb:block choices j0.succ=[]
  · simp only [value,OmittedAssignmentIdentity.testValue,hb,ite_true,
      NativeFirstOmittedMoments.word,NativeFirstOmittedMoments.collapse]
    ring
  · simp only [value,OmittedAssignmentIdentity.testValue,hb,ite_false,mul_zero]

theorem value_integrable
    (A:Fin r→MeasurableGeneralizedInverse.Mat n) (D:Fin r→State n)
    (R C:MeasurableGeneralizedInverse.Mat n) (E:State n)
    (choices:List (Fin r×Fin (m+1))) (j0:Fin m) (a:ℝ→ℝ) (ha:Measurable a)
    (F:State d→ℝ) (hF:Measurable F) (mean:State n) (g:Fin d→Fin n)
    (leaf:Fin m→Fin n) (baseline:Fin m→ℝ)
    {K M:ℝ} (hK:0≤K) (hFb:∀z,|F z|≤K) (hab:∀z,|a z|≤M):
    Integrable (value A D R E choices j0 a F mean g leaf baseline)
      ((Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod
        ((multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C))):=by
  have hs:=Integrable.fintype_prod (fun j=>gaussian_secondScore_integrable (A j) (D j))
  have hnative:Integrable (fun fresh:State n×State n=>firstScore R E fresh.1)
      ((multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C)):=
    (FiniteWordScores.firstScore_integrable R E).comp_fst _
  have hp:Measurable (fun z:(Fin r→State n)×(State n×State n)=>(z.1,z.2.1+z.2.2)):=by fun_prop
  exact (hs.mul_prod hnative).mul_bdd
    ((OmittedAssignmentIdentity.testValue_measurable choices j0 a ha F hF g leaf baseline mean).comp hp).aestronglyMeasurable
    (ae_of_all _ (fun z=>by simpa only [Real.norm_eq_abs] using
      OmittedAssignmentIdentity.testValue_bound choices j0 a F g leaf baseline hK hFb hab mean (z.1,z.2.1+z.2.2)))

theorem sum_value (A:Fin r→MeasurableGeneralizedInverse.Mat n) (D:Fin r→State n)
    (R:MeasurableGeneralizedInverse.Mat n) (E:State n)
    (cs:List (List (Fin r×Fin (m+1)))) (j0:Fin m) (a:ℝ→ℝ) (F:State d→ℝ)
    (mean:State n) (g:Fin d→Fin n) (leaf:Fin m→Fin n) (baseline:Fin m→ℝ)
    (old:Fin r→State n) (fresh:State n×State n):
    (cs.map (fun choices=>value A D R E choices j0 a F mean g leaf baseline (old,fresh))).sum=
      ((∏j,secondScore (A j) (D j) (old j))*
        (cs.map (fun choices=>OmittedAssignmentIdentity.testValue choices j0 a F g leaf baseline
          mean (old,fresh.1+fresh.2))).sum)*firstScore R E fresh.1:=by
  induction cs with
  | nil=>simp
  | cons choices cs ih=>
    simp only [List.map_cons,List.sum_cons]
    rw [ih]
    simp only [value,NativeFirstOldScoreMoments.scores]
    ring

/-- Exact omitted-word assignment with native FIRST score and an
UNSCORED remaining law. A nonempty deleted-leaf block vanishes before
any estimate; its other original blocks and baselines are unchanged. -/
theorem assignment_integral
    (A:Fin r→MeasurableGeneralizedInverse.Mat n) (hA:∀j,(A j).PosSemidef)
    (D:Fin r→State n) (hD:∀j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A j)).range)
    (R C:MeasurableGeneralizedInverse.Mat n) (E:State n)
    (is:List (Fin r)) (hnd:is.Nodup) (j0:Fin m) (a:ℝ→ℝ) (ha:Measurable a)
    (F:State d→ℝ) (hF:Measurable F) (mean:State n) (g:Fin d→Fin n)
    (leaf:Fin m→Fin n) (baseline:Fin m→ℝ)
    {K M:ℝ} (hK:0≤K) (hFb:∀z,|F z|≤K) (hab:∀z,|a z|≤M):
    (∫fresh:State n×State n,(∫old,(∏j,secondScore (A j) (D j) (old j))*
        OmittedAssignmentIdentity.raw a F g leaf baseline j0 (mean+(fresh.1+fresh.2)+∑j,old j)
        ∂Measure.pi (fun j=>multivariateGaussian (0:State n) (A j)))*firstScore R E fresh.1
      ∂(multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C))=
      ((assignments (m:=m+1) is).map (fun choices=>∫z,
        value A D R E choices j0 a F mean g leaf baseline z
        ∂(Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod
          ((multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C)))).sum:=by
  let cs:=assignments (m:=m+1) is
  let μ:=(Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod
    ((multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C))
  have hi(choices):Integrable (value A D R E choices j0 a F mean g leaf baseline) μ:=
    value_integrable A D R C E choices j0 a ha F hF mean g leaf baseline hK hFb hab
  let W:=fun z=>(cs.map (fun choices=>value A D R E choices j0 a F mean g leaf baseline z)).sum
  have hW:Integrable W μ:=GaussianFreshSum.integrable_sum μ cs _ (fun choices _=>hi choices)
  have hif:Integrable (Function.uncurry (fun (old:Fin r→State n) (fresh:State n×State n)=>W (old,fresh))) μ:=by
    convert! hW using 1
  rw [←GaussianFreshSum.integral_sum μ cs _ (fun choices _=>hi choices),integral_prod _ hW,
    integral_integral_swap hif]
  apply integral_congr_ae
  exact ae_of_all _ (fun fresh=>by
    dsimp only
    rw [OmittedAssignmentIdentity.old_average_eq A hA D hD is hnd a ha F hF g leaf baseline j0 hK hFb hab mean (fresh.1+fresh.2)]
    rw [←integral_mul_const]
    apply integral_congr_ae
    exact ae_of_all _ (fun old=>(sum_value A D R E cs j0 a F mean g leaf baseline old fresh).symm))

end SHE.NativeFirstOmittedAssignment
