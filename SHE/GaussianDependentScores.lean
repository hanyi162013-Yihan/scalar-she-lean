module

public import SHE.DependentProducts
public import SHE.MeasurableGaussianScores

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

/-! Every fixed finite product of actual canonical first and second
Gaussian scores has a variance-scaled bound even when all projections
are correlated and the covariance is singular. -/
namespace SHE.GaussianDependentScores
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAudit
  MeasurableGaussianScores DependentProducts ProfileL2
open scoped InnerProductSpace BigOperators

def factor {d:ℕ}(second:Bool)(A:Matrix (Fin d) (Fin d) ℝ)(D y:State d):ℝ:=
  if second then secondScore A D y else firstScore A D y

def scale {d:ℕ}(second:Bool)(A:Matrix (Fin d) (Fin d) ℝ)(D:State d):ℝ:=
  if second then scoreVariance A D else sqrt (scoreVariance A D)

def productMomentConstant (n:ℕ):ℝ:=max (firstScoreMoment n) (secondScoreMoment n)

theorem productMomentConstant_nonneg (n:ℕ):0≤productMomentConstant n:=
  (firstScoreMoment_nonneg n).trans (le_max_left _ _)

theorem factor_measurable {d:ℕ}(second:Bool)(A:Matrix (Fin d) (Fin d) ℝ)(D:State d):
    Measurable (factor second A D):=by
  cases second
  · change Measurable (MeasurableGaussianScores.firstScore A D)
    exact (innerSL ℝ (MeasurableGaussianScores.coefficient A D)).continuous.measurable
  · change Measurable (MeasurableGaussianScores.secondScore A D)
    exact ((innerSL ℝ (MeasurableGaussianScores.coefficient A D)).continuous.measurable.pow_const 2).sub measurable_const

theorem scale_nonneg {d:ℕ}{A:Matrix (Fin d) (Fin d) ℝ}(hA:A.PosSemidef){D:State d}
    (hD:D∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range)(second:Bool):0≤scale second A D:=by
  cases second
  · exact sqrt_nonneg _
  · exact scoreVariance_nonneg hA hD

theorem factor_even_moment {d:ℕ}{A:Matrix (Fin d) (Fin d) ℝ}(hA:A.PosSemidef){D:State d}
    (hD:D∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range)(second:Bool)(n:ℕ):
    Integrable (fun y=>|factor second A D y|^(2*n)) (multivariateGaussian 0 A) ∧
      (∫y,|factor second A D y|^(2*n) ∂multivariateGaussian 0 A)≤
        productMomentConstant n*scale second A D^(2*n):=by
  have hv:=scoreVariance_nonneg hA hD
  cases second
  · have hm:=firstScore_even_moments hA hD n
    refine ⟨hm.1,?_⟩
    change (∫y,|firstScore A D y|^(2*n) ∂multivariateGaussian 0 A)≤
      productMomentConstant n*(sqrt (scoreVariance A D))^(2*n)
    rw[hm.2,pow_mul,sq_sqrt hv]
    have hc:firstScoreMoment n≤productMomentConstant n:=le_max_left _ _
    exact (mul_le_mul_of_nonneg_left hc (pow_nonneg hv _)).trans_eq (by ring)
  · have hm:=secondScore_even_moments hA hD n
    refine ⟨hm.1,?_⟩
    change (∫y,|secondScore A D y|^(2*n) ∂multivariateGaussian 0 A)≤
      productMomentConstant n*scoreVariance A D^(2*n)
    rw[hm.2]
    have hc:secondScoreMoment n≤productMomentConstant n:=le_max_right _ _
    exact (mul_le_mul_of_nonneg_left hc (pow_nonneg hv _)).trans_eq (by ring)

/-- The sole constant depends on the finite number of score factors.
Every physical mean or covariance energy appears with its exact degree. -/
theorem product_normTwo {d n:ℕ}(hn:0<n){A:Matrix (Fin d) (Fin d) ℝ}(hA:A.PosSemidef)
    (D:Fin n→State d)(hD:∀i,D i∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range)(second:Fin n→Bool):
    normTwo (multivariateGaussian 0 A) (fun y=>∏i,factor (second i) A (D i) y)≤
      sqrt (productMomentConstant n)*(∏i,scale (second i) A (D i)):=by
  exact product_normTwo_bound (multivariateGaussian 0 A) hn
    (fun i=>factor (second i) A (D i)) (fun i=>factor_measurable _ _ _)
    (fun i=>scale (second i) A (D i)) (fun i=>scale_nonneg hA (hD i) _)
    (fun i=>(factor_even_moment hA (hD i) (second i) n).1)
    (productMomentConstant_nonneg n) (fun i=>(factor_even_moment hA (hD i) (second i) n).2)

end SHE.GaussianDependentScores
