module

public import SHE.GaussianOldFreshWord
public import SHE.NativeFirstWholeAverage
public import SHE.TwoFreshAverageOrder

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace SHE.NativeFirstWholeAssignment
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianAssignmentBlocks
  GaussianDependentScores MeasurableGaussianScores GaussianConvolution GaussianVectorFractions
open scoped BigOperators
variable {n d r m:ℕ}

theorem word_integrable     (A:Fin r→MeasurableGeneralizedInverse.Mat n) (D:Fin r→State n)
    (R C:MeasurableGeneralizedInverse.Mat n)     (E:State n)
    (choices:List (Fin r×Fin (m+1))) (a:ℝ→ℝ) (ha:Measurable a)
    (F:State d→ℝ) (hF:Measurable F) (mean:State n) (g:Fin d→Fin n)
    (leaf:Fin m→Fin n) (baseline:Fin m→ℝ)
    {K M:ℝ} (hK:0≤K) (hFb:∀z,|F z|≤K) (hab:∀z,|a z|≤M):
    Integrable (fun z=>NativeFirstWholeMoments.word A D R E choices
      a F (fun _:Unit=>mean) g leaf baseline ((),z))
      ((Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod
        ((multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C))):=by
  have hh:=GaussianOldFreshWord.value_integrable
    ((multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C)) A D
    (fun z:State n×State n=>firstScore R E z.1)
    ((FiniteWordScores.firstScore_integrable R E).comp_fst _)
    (fun z:State n×State n=>z.1+z.2) (measurable_fst.add measurable_snd)
    choices a ha F hF mean g leaf baseline hK hFb hab
  convert! hh using 1
  funext z
  simp only [GaussianOldFreshWord.value,NativeFirstWholeMoments.word,
    NativeFirstOldScoreMoments.scores,NativeFirstWholeMoments.collapse]
  ring

/-- The exact old assignment sum under the untouched native and fresh
Gaussian score carriers. Both scores are evaluated in their ORIGINAL
fractions; all test factors see their sum. -/
theorem assignment_integral     (A:Fin r→MeasurableGeneralizedInverse.Mat n) (hA:∀j,(A j).PosSemidef)
    (D:Fin r→State n) (hD:∀j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A j)).range)
    (R C:MeasurableGeneralizedInverse.Mat n)     (E:State n)
    (is:List (Fin r)) (hnd:is.Nodup) (a:ℝ→ℝ) (ha:Measurable a)
    (F:State d→ℝ) (hF:Measurable F) (mean:State n) (g:Fin d→Fin n)
    (leaf:Fin m→Fin n) (baseline:Fin m→ℝ)
    {K M:ℝ} (hK:0≤K) (hFb:∀z,|F z|≤K) (hab:∀z,|a z|≤M):
    (∫fresh:State n×State n,(∫old,(∏j,secondScore (A j) (D j) (old j))*
        VectorAssignmentIdentity.raw a F g leaf baseline (mean+(fresh.1+fresh.2)+∑j,old j)
        ∂Measure.pi (fun j=>multivariateGaussian (0:State n) (A j)))*
          firstScore R E fresh.1
      ∂(multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C))=
      ((assignments (m:=m+1) is).map (fun choices=>∫z,
        NativeFirstWholeMoments.word A D R E choices a F
          (fun _:Unit=>mean) g leaf baseline ((),z)
        ∂(Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod
          ((multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C)))).sum:=by
  have hh:=GaussianOldFreshWord.assignment_integral
    ((multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C)) A hA D hD
    (fun z:State n×State n=>firstScore R E z.1)
    ((FiniteWordScores.firstScore_integrable R E).comp_fst _)
    (fun z:State n×State n=>z.1+z.2) (measurable_fst.add measurable_snd)
    is hnd a ha F hF mean g leaf baseline hK hFb hab
  convert! hh using 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro choices _
  apply integral_congr_ae
  exact ae_of_all _ (fun z=>by
    simp only [GaussianOldFreshWord.value,NativeFirstWholeMoments.word,
      NativeFirstOldScoreMoments.scores,NativeFirstWholeMoments.collapse]
    ring)



theorem average (A:Fin r→MeasurableGeneralizedInverse.Mat n) (hA:∀j,(A j).PosSemidef)
    (D:Fin r→State n) (hD:∀j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A j)).range)
    (R C:MeasurableGeneralizedInverse.Mat n) (E:State n)
    (is:List (Fin r)) (hnd:is.Nodup) (a:ℝ→ℝ) (ha:Measurable a)
    (F:State d→ℝ) (hF:Measurable F) (mean:State n) (g:Fin d→Fin n)
    (leaf:Fin m→Fin n) (baseline:Fin m→ℝ)
    {K M:ℝ} (hK:0≤K) (hFb:∀z,|F z|≤K) (hab:∀z,|a z|≤M):
    gaussianAverage C
      (WeightedBorelAverage.average
        ((Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod
          (multivariateGaussian (0:State n) R))
        (GaussianFixedFirstAverage.weight R E (fun old=>∏j,secondScore (A j) (D j) (old j)))
        (GaussianFixedFirstAverage.shift (fun old=>∑j,old j))
        (VectorAssignmentIdentity.raw a F g leaf baseline)) mean=
      ((assignments (m:=m+1) is).map (fun choices=>∫z,
        NativeFirstWholeMoments.word A D R E choices a F (fun _:Unit=>mean) g leaf baseline ((),z)
        ∂(Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod
          ((multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C)))).sum:=by
  let μ:=Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))
  let w:=fun old:Fin r→State n=>∏j,secondScore (A j) (D j) (old j)
  have hw:Integrable w μ:=Integrable.fintype_prod (fun j=>gaussian_secondScore_integrable (A j) (D j))
  have hwm:Measurable w:=Finset.measurable_prod Finset.univ (fun j _=>
    (factor_measurable true (A j) (D j)).comp (measurable_pi_apply j))
  have hs:Measurable (fun old:Fin r→State n=>∑j,old j):=by fun_prop
  have hraw:Measurable (VectorAssignmentIdentity.raw a F g leaf baseline):=by
    unfold VectorAssignmentIdentity.raw
    fun_prop
  let B:=K*∏j∈Finset.univ,(M+|baseline j|)
  have hM:0≤M:=(abs_nonneg _).trans (hab 0)
  have hB:0≤B:=mul_nonneg hK (Finset.prod_nonneg (fun j _=>add_nonneg hM (abs_nonneg _)))
  have hbb:∀z,|VectorAssignmentIdentity.raw a F g leaf baseline z|≤B:=
    VectorAssignmentIdentity.raw_bound a F g leaf baseline hK hFb hab
  have ho:=TwoFreshAverageOrder.order μ R C E w hw hwm _ hs (fun _=>1) (integrable_const 1)
    _ hraw B hB hbb mean
  calc
    _=WeightedBorelAverage.average
        ((multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C))
        (fun fresh:State n×State n=>firstScore R E fresh.1) (fun fresh=>fresh.1+fresh.2)
        (WeightedBorelAverage.average μ w (fun old=>∑j,old j)
          (VectorAssignmentIdentity.raw a F g leaf baseline)) mean:=by
      simpa only [gaussianAverage,WeightedBorelAverage.average,id_eq,one_mul,mul_one] using ho
    _=(∫fresh:State n×State n,(∫old,(∏j,secondScore (A j) (D j) (old j))*
        VectorAssignmentIdentity.raw a F g leaf baseline (mean+(fresh.1+fresh.2)+∑j,old j)
        ∂μ)*firstScore R E fresh.1
      ∂(multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C)):=by
      unfold WeightedBorelAverage.average
      apply integral_congr_ae
      exact ae_of_all _ (fun fresh=>by dsimp only;ring)
    _=_:=assignment_integral A hA D hD R C E is hnd a ha F hF mean g leaf baseline hK hFb hab


end SHE.NativeFirstWholeAssignment
