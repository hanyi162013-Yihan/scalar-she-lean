module

public import SHE.TwoFreshAverageOrder

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SHE.TwoFreshWholeWordAssignments
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution
  GaussianAssignmentBlocks GaussianVectorFractions GaussianDependentScores MeasurableGaussianScores
open scoped BigOperators
variable {n d r m:ℕ}

/-- The literal old-weighted complete centered word, with its native
first score in the fixed product weight and its fresh first/second mark
outside, is EXACTLY the finite sum of the quantitative assigned fibres. -/
theorem score_average (second:Bool)
    (A:Fin r→MeasurableGeneralizedInverse.Mat n) (hA:∀j,(A j).PosSemidef)
    (D:Fin r→State n) (hD:∀j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A j)).range)
    (R C:MeasurableGeneralizedInverse.Mat n) (hR:R.PosSemidef) (hC:C.PosSemidef)
    (E V:State n) (hE:E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) R).range)
    (hV:V∈(Matrix.toEuclideanCLM (𝕜:=ℝ) C).range)
    (is:List (Fin r)) (hnd:is.Nodup) (a:ℝ→ℝ) (ha:Measurable a)
    (F:State d→ℝ) (hF:Measurable F) (mean:State n) (g:Fin d→Fin n)
    (leaf:Fin m→Fin n) (baseline:Fin m→ℝ)
    {K M:ℝ} (hK:0≤K) (hFb:∀z,|F z|≤K) (hab:∀z,|a z|≤M):
    WeightedBorelAverage.average (multivariateGaussian (0:State n) C) (factor second C V) id
      (WeightedBorelAverage.average
        ((Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod
          (multivariateGaussian (0:State n) R))
        (GaussianFixedFirstAverage.weight R E (fun old=>∏j,secondScore (A j) (D j) (old j)))
        (GaussianFixedFirstAverage.shift (fun old=>∑j,old j))
        (VectorAssignmentIdentity.raw a F g leaf baseline)) mean=
      ((assignments (m:=m+1) is).map (fun choices=>∫z,
        TwoFreshFullResidualMoments.word second A D R C E V choices a F
          (fun _:Unit=>mean) g leaf baseline ((),z)
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
  let B:=K*∏j:Fin m,(M+|baseline j|)
  have hM:0≤M:=(abs_nonneg _).trans (hab 0)
  have hB:0≤B:=mul_nonneg hK (Finset.prod_nonneg (fun j _=>add_nonneg hM (abs_nonneg _)))
  have hbb:∀z,|VectorAssignmentIdentity.raw a F g leaf baseline z|≤B:=
    VectorAssignmentIdentity.raw_bound a F g leaf baseline hK hFb hab
  rw [TwoFreshAverageOrder.score_order μ second R C hC E V hV w hw hwm _ hs
    _ hraw B hB hbb mean]
  calc
    _=(∫fresh:State n×State n,(∫old,(∏j,secondScore (A j) (D j) (old j))*
        VectorAssignmentIdentity.raw a F g leaf baseline (mean+(fresh.1+fresh.2)+∑j,old j)
        ∂μ)*(firstScore R E fresh.1*factor second C V fresh.2)
      ∂(multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C)):=by
        unfold WeightedBorelAverage.average
        apply integral_congr_ae
        exact ae_of_all _ (fun fresh=>by dsimp only [id_eq];ring)
    _=_:=TwoFreshAssignmentIntegral.assignment_integral second A hA D hD R C hR hC E V hE hV
      is hnd a ha F hF mean g leaf baseline hK hFb hab

end SHE.TwoFreshWholeWordAssignments
