module

public import SHE.NativeFirstOmittedAssignment

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SHE.NativeFirstOmittedWholeAverage
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution
  GaussianAssignmentBlocks GaussianVectorFractions GaussianDependentScores MeasurableGaussianScores
open scoped BigOperators
variable {n d r m:ℕ}

/-- The original Gaussian omitted-baseline average with the unchanged
native first-score weight equals its exact canonical assignment sum.
The remaining Gaussian C is UNSCORED, and nonempty deleted blocks vanish. -/
theorem average (A:Fin r→MeasurableGeneralizedInverse.Mat n) (hA:∀j,(A j).PosSemidef)
    (D:Fin r→State n) (hD:∀j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A j)).range)
    (R C:MeasurableGeneralizedInverse.Mat n) (E:State n)
    (is:List (Fin r)) (hnd:is.Nodup) (j0:Fin m) (a:ℝ→ℝ) (ha:Measurable a)
    (F:State d→ℝ) (hF:Measurable F) (mean:State n) (g:Fin d→Fin n)
    (leaf:Fin m→Fin n) (baseline:Fin m→ℝ)
    {K M:ℝ} (hK:0≤K) (hFb:∀z,|F z|≤K) (hab:∀z,|a z|≤M):
    gaussianAverage C
      (WeightedBorelAverage.average
        ((Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod
          (multivariateGaussian (0:State n) R))
        (GaussianFixedFirstAverage.weight R E (fun old=>∏j,secondScore (A j) (D j) (old j)))
        (GaussianFixedFirstAverage.shift (fun old=>∑j,old j))
        (OmittedAssignmentIdentity.raw a F g leaf baseline j0)) mean=
      ((assignments (m:=m+1) is).map (fun choices=>∫z,
        NativeFirstOmittedAssignment.value A D R E choices j0 a F mean g leaf baseline z
        ∂(Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod
          ((multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C)))).sum:=by
  let μ:=Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))
  let w:=fun old:Fin r→State n=>∏j,secondScore (A j) (D j) (old j)
  have hw:Integrable w μ:=Integrable.fintype_prod (fun j=>gaussian_secondScore_integrable (A j) (D j))
  have hwm:Measurable w:=Finset.measurable_prod Finset.univ (fun j _=>
    (factor_measurable true (A j) (D j)).comp (measurable_pi_apply j))
  have hs:Measurable (fun old:Fin r→State n=>∑j,old j):=by fun_prop
  have hraw:Measurable (OmittedAssignmentIdentity.raw a F g leaf baseline j0):=by
    unfold OmittedAssignmentIdentity.raw
    fun_prop
  let B:=K*∏j∈Finset.univ.erase j0,(M+|baseline j|)
  have hM:0≤M:=(abs_nonneg _).trans (hab 0)
  have hB:0≤B:=mul_nonneg hK (Finset.prod_nonneg (fun j _=>add_nonneg hM (abs_nonneg _)))
  have hbb:∀z,|OmittedAssignmentIdentity.raw a F g leaf baseline j0 z|≤B:=
    OmittedAssignmentIdentity.raw_bound a F g leaf baseline j0 hK hFb hab
  have ho:=TwoFreshAverageOrder.order μ R C E w hw hwm _ hs (fun _=>1) (integrable_const 1)
    _ hraw B hB hbb mean
  calc
    _=WeightedBorelAverage.average
        ((multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C))
        (fun fresh:State n×State n=>firstScore R E fresh.1) (fun fresh=>fresh.1+fresh.2)
        (WeightedBorelAverage.average μ w (fun old=>∑j,old j)
          (OmittedAssignmentIdentity.raw a F g leaf baseline j0)) mean:=by
      simpa only [gaussianAverage,WeightedBorelAverage.average,id_eq,one_mul,mul_one] using ho
    _=(∫fresh:State n×State n,(∫old,(∏j,secondScore (A j) (D j) (old j))*
        OmittedAssignmentIdentity.raw a F g leaf baseline j0 (mean+(fresh.1+fresh.2)+∑j,old j)
        ∂μ)*firstScore R E fresh.1
      ∂(multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C)):=by
      unfold WeightedBorelAverage.average
      apply integral_congr_ae
      exact ae_of_all _ (fun fresh=>by dsimp only;ring)
    _=_:=NativeFirstOmittedAssignment.assignment_integral A hA D hD R C E is hnd j0 a ha F hF mean g leaf baseline hK hFb hab

end SHE.NativeFirstOmittedWholeAverage
