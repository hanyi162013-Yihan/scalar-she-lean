module

public import SHE.TwoFreshAssignmentIntegral
public import SHE.GaussianFixedFirstAverage

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace SHE.TwoFreshAverageOrder
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution
  GaussianDependentScores MeasurableGaussianScores
variable {X:Type*} [MeasurableSpace X] {n:ℕ}

/-- Exact averaging order for an untouched native first score and an
arbitrary integrable fresh weight. It applies both to Gaussian mean and
covariance scores and to the unscored omitted-baseline law. -/
theorem order (μ:Measure X) [SFinite μ]
    (R C:MeasurableGeneralizedInverse.Mat n) (E:State n)
    (w:X→ℝ) (hw:Integrable w μ) (hwm:Measurable w)
    (shift:X→State n) (hs:Measurable shift)
    (v:State n→ℝ) (hv:Integrable v (multivariateGaussian (0:State n) C))
    (F:State n→ℝ) (hF:Measurable F) (M:ℝ) (hM:0≤M) (hb:∀z,|F z|≤M) (mean:State n):
    WeightedBorelAverage.average (multivariateGaussian (0:State n) C) v id
      (WeightedBorelAverage.average (μ.prod (multivariateGaussian (0:State n) R))
        (GaussianFixedFirstAverage.weight R E w) (GaussianFixedFirstAverage.shift shift) F) mean=
    WeightedBorelAverage.average
      ((multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C))
      (fun z:State n×State n=>firstScore R E z.1*v z.2) (fun z=>z.1+z.2)
      (WeightedBorelAverage.average μ w shift F) mean:=by
  let G:=WeightedBorelAverage.average μ w shift F
  have hG:Measurable G:=WeightedBorelAverage.measurable μ w hwm shift hs F hF
  have hGb:∀z,|G z|≤M*∫x,|w x| ∂μ:=WeightedBorelAverage.bound μ w hw shift hs F hF M hM hb
  have he:WeightedBorelAverage.average (μ.prod (multivariateGaussian (0:State n) R))
      (GaussianFixedFirstAverage.weight R E w) (GaussianFixedFirstAverage.shift shift) F=
      WeightedBorelAverage.average (multivariateGaussian (0:State n) R) (firstScore R E) id G:=by
    funext z
    exact (GaussianFixedFirstAverage.old_average μ R E w hw shift hs F hF M hb z).symm
  rw [he]
  rw [WeightedAverageProduct.commute (multivariateGaussian (0:State n) C)
    (multivariateGaussian (0:State n) R) v (firstScore R E) hv
    (FiniteWordScores.firstScore_integrable R E) id id measurable_id measurable_id G hG
    (M*∫x,|w x| ∂μ) hGb]
  exact WeightedAverageProduct.product (multivariateGaussian (0:State n) R)
    (multivariateGaussian (0:State n) C) (firstScore R E) v
    (FiniteWordScores.firstScore_integrable R E) hv id id measurable_id measurable_id G hG
    (M*∫x,|w x| ∂μ) hGb mean

/-- The fresh Gaussian first/second mark, in its original averaging
order, retains the exact same two independent score carriers. -/
theorem score_order (μ:Measure X) [SFinite μ] (second:Bool)
    (R C:MeasurableGeneralizedInverse.Mat n) (hC:C.PosSemidef) (E V:State n)
    (hV:V∈(Matrix.toEuclideanCLM (𝕜:=ℝ) C).range)
    (w:X→ℝ) (hw:Integrable w μ) (hwm:Measurable w)
    (shift:X→State n) (hs:Measurable shift)
    (F:State n→ℝ) (hF:Measurable F) (M:ℝ) (hM:0≤M) (hb:∀z,|F z|≤M) (mean:State n):
    WeightedBorelAverage.average (multivariateGaussian (0:State n) C) (factor second C V) id
      (WeightedBorelAverage.average (μ.prod (multivariateGaussian (0:State n) R))
        (GaussianFixedFirstAverage.weight R E w) (GaussianFixedFirstAverage.shift shift) F) mean=
    WeightedBorelAverage.average
      ((multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C))
      (fun z:State n×State n=>firstScore R E z.1*factor second C V z.2) (fun z=>z.1+z.2)
      (WeightedBorelAverage.average μ w shift F) mean:=
  order μ R C E w hw hwm shift hs (factor second C V)
    (TwoFreshAssignmentIntegral.factor_integrable C hC V hV second) F hF M hM hb mean

end SHE.TwoFreshAverageOrder
