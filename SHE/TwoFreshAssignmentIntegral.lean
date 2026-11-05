module

public import SHE.GaussianOldFreshWord
public import SHE.TwoFreshAssignedAverage

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace SHE.TwoFreshAssignmentIntegral
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianAssignmentBlocks
  GaussianDependentScores MeasurableGaussianScores
open scoped BigOperators
variable {n d r m:ℕ}

theorem factor_integrable (A:MeasurableGeneralizedInverse.Mat n) (hA:A.PosSemidef)
    (E:State n) (hE:E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range) (second:Bool):
    Integrable (factor second A E) (multivariateGaussian (0:State n) A):=by
  have hh:MemLp (factor second A E) 2 (multivariateGaussian (0:State n) A):=
    (memLp_two_iff_integrable_sq (factor_measurable second A E).aestronglyMeasurable).mpr
      (by simpa only [Nat.mul_one,sq_abs] using (factor_even_moment hA hE second 1).1)
  exact hh.integrable (by norm_num)

theorem fresh_weight_integrable (second:Bool) (R C:MeasurableGeneralizedInverse.Mat n)
    (hR:R.PosSemidef) (hC:C.PosSemidef) (E V:State n)
    (hE:E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) R).range)
    (hV:V∈(Matrix.toEuclideanCLM (𝕜:=ℝ) C).range):
    Integrable (fun z:State n×State n=>firstScore R E z.1*factor second C V z.2)
      ((multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C)):=by
  exact (factor_integrable R hR E hE false).mul_prod (factor_integrable C hC V hV second)

theorem word_integrable (second:Bool)
    (A:Fin r→MeasurableGeneralizedInverse.Mat n) (D:Fin r→State n)
    (R C:MeasurableGeneralizedInverse.Mat n) (hR:R.PosSemidef) (hC:C.PosSemidef)
    (E V:State n) (hE:E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) R).range)
    (hV:V∈(Matrix.toEuclideanCLM (𝕜:=ℝ) C).range)
    (choices:List (Fin r×Fin (m+1))) (a:ℝ→ℝ) (ha:Measurable a)
    (F:State d→ℝ) (hF:Measurable F) (mean:State n) (g:Fin d→Fin n)
    (leaf:Fin m→Fin n) (baseline:Fin m→ℝ)
    {K M:ℝ} (hK:0≤K) (hFb:∀z,|F z|≤K) (hab:∀z,|a z|≤M):
    Integrable (fun z=>TwoFreshFullResidualMoments.word second A D R C E V choices
      a F (fun _:Unit=>mean) g leaf baseline ((),z))
      ((Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod
        ((multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C))):=by
  have hh:=GaussianOldFreshWord.value_integrable
    ((multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C)) A D
    (fun z:State n×State n=>firstScore R E z.1*factor second C V z.2)
    (fresh_weight_integrable second R C hR hC E V hE hV)
    (fun z:State n×State n=>z.1+z.2) (measurable_fst.add measurable_snd)
    choices a ha F hF mean g leaf baseline hK hFb hab
  convert! hh using 1
  funext z
  simp only [GaussianOldFreshWord.value,TwoFreshFullResidualMoments.word,
    TwoFreshGaussianFractions.scores,TwoFreshFullResidualMoments.collapse]
  ring

/-- The exact old assignment sum under the untouched native and fresh
Gaussian score carriers. Both scores are evaluated in their ORIGINAL
fractions; all test factors see their sum. -/
theorem assignment_integral (second:Bool)
    (A:Fin r→MeasurableGeneralizedInverse.Mat n) (hA:∀j,(A j).PosSemidef)
    (D:Fin r→State n) (hD:∀j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A j)).range)
    (R C:MeasurableGeneralizedInverse.Mat n) (hR:R.PosSemidef) (hC:C.PosSemidef)
    (E V:State n) (hE:E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) R).range)
    (hV:V∈(Matrix.toEuclideanCLM (𝕜:=ℝ) C).range)
    (is:List (Fin r)) (hnd:is.Nodup) (a:ℝ→ℝ) (ha:Measurable a)
    (F:State d→ℝ) (hF:Measurable F) (mean:State n) (g:Fin d→Fin n)
    (leaf:Fin m→Fin n) (baseline:Fin m→ℝ)
    {K M:ℝ} (hK:0≤K) (hFb:∀z,|F z|≤K) (hab:∀z,|a z|≤M):
    (∫fresh:State n×State n,(∫old,(∏j,secondScore (A j) (D j) (old j))*
        VectorAssignmentIdentity.raw a F g leaf baseline (mean+(fresh.1+fresh.2)+∑j,old j)
        ∂Measure.pi (fun j=>multivariateGaussian (0:State n) (A j)))*
          (firstScore R E fresh.1*factor second C V fresh.2)
      ∂(multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C))=
      ((assignments (m:=m+1) is).map (fun choices=>∫z,
        TwoFreshFullResidualMoments.word second A D R C E V choices a F
          (fun _:Unit=>mean) g leaf baseline ((),z)
        ∂(Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod
          ((multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C)))).sum:=by
  have hh:=GaussianOldFreshWord.assignment_integral
    ((multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C)) A hA D hD
    (fun z:State n×State n=>firstScore R E z.1*factor second C V z.2)
    (fresh_weight_integrable second R C hR hC E V hE hV)
    (fun z:State n×State n=>z.1+z.2) (measurable_fst.add measurable_snd)
    is hnd a ha F hF mean g leaf baseline hK hFb hab
  convert! hh using 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro choices _
  apply integral_congr_ae
  exact ae_of_all _ (fun z=>by
    simp only [GaussianOldFreshWord.value,TwoFreshFullResidualMoments.word,
      TwoFreshGaussianFractions.scores,TwoFreshFullResidualMoments.collapse]
    ring)

end SHE.TwoFreshAssignmentIntegral
