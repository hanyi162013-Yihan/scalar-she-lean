module

public import SHE.OldIntervalGaussian
public import SHE.GaussianDependentScores
public import SHE.GaussianEnvelopeMoments
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.OldIntervalScoreMoments
open Set MeasureTheory ProbabilityTheory Real AddCircle GaussianIncrement GaussianAudit
  MeasurableGaussianScores GaussianEnvelopeMoments OldIntervalCovariance StoppedGaussianFeatures StoppedFourier
open scoped NNReal InnerProductSpace BigOperators
local instance : Fact (0<2*π):=⟨by positivity⟩

/-- All old covariance score factors have their actual fixed moments
under the literal product law. This factorization concerns only the
independent old increments, never the dependent rough test factors. -/
theorem product_even_moment {n r:ℕ}(A:Fin r→Matrix (Fin n) (Fin n) ℝ)(hA:∀j,(A j).PosSemidef)
    (D:Fin r→State n)(hD:∀j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A j)).range)(p:ℕ):
    Integrable (fun y:Fin r→State n=>|∏j,secondScore (A j) (D j) (y j)|^(2*p))
      (Measure.pi (fun j=>multivariateGaussian 0 (A j))) ∧
    (∫y:Fin r→State n,|∏j,secondScore (A j) (D j) (y j)|^(2*p)
      ∂Measure.pi (fun j=>multivariateGaussian 0 (A j)))=
      (secondScoreMoment p)^r*(∏j,scoreVariance (A j) (D j))^(2*p):=by
  have hi (j:Fin r):Integrable (fun y=>|secondScore (A j) (D j) y|^(2*p)) (multivariateGaussian 0 (A j)):=
    (secondScore_even_moments (hA j) (hD j) p).1
  have he (y:Fin r→State n):|∏j,secondScore (A j) (D j) (y j)|^(2*p)=
      ∏j,|secondScore (A j) (D j) (y j)|^(2*p):=by rw[Finset.abs_prod,Finset.prod_pow]
  constructor
  · simp_rw[he]
    exact Integrable.fintype_prod hi
  · simp_rw[he]
    have hfub:=integral_fintype_prod_eq_prod (μ:=fun j=>multivariateGaussian (0:State n) (A j))
      (fun (j:Fin r) (z:State n)=>|secondScore (A j) (D j) z|^(2*p))
    change (∫y:Fin r→State n,∏j,|secondScore (A j) (D j) (y j)|^(2*p)
      ∂Measure.pi (fun j=>multivariateGaussian 0 (A j)))=_ at hfub
    rw[hfub]
    simp_rw[fun j=>(secondScore_even_moments (hA j) (hD j) p).2]
    rw[Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,Finset.prod_pow]
    ring

theorem projection_hasLaw {n r:ℕ}(A:Fin r→Matrix (Fin n) (Fin n) ℝ)(hA:∀j,(A j).PosSemidef)
    (D:Fin r→State n)(hD:∀j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A j)).range)(i:Fin r):
    HasLaw (fun y:Fin r→State n=>firstScore (A i) (D i) (y i))
      (gaussianReal 0 (scoreVariance (A i) (D i)).toNNReal)
      (Measure.pi (fun j=>multivariateGaussian 0 (A j))):=by
  let μ:=fun j=>multivariateGaussian (0:State n) (A j)
  let L:=innerSL ℝ (MeasurableGaussianScores.coefficient (A i) (D i))
  have hL:(∫y,L y ∂μ i)=0:=firstScore_mean_zero (A i) (D i)
  have hLaw:=GaussianEnvelopeMoments.projection_hasLaw (μ i) L hL
  rw[firstScore_variance (hA i) (hD i)] at hLaw
  have heval:HasLaw (fun y:Fin r→State n=>y i) (μ i) (Measure.pi μ):=
    ⟨(measurable_pi_apply i).aemeasurable,(measurePreserving_eval μ i).map_eq⟩
  exact hLaw.fun_comp heval

/-- All applicability conditions for the genuine physical old interval
family are discharged, including singular ranges at the insertion rows. -/
theorem actual_product_even_moment_ae {n r:ℕ}(σ target:Fin n→ℝ)(center:Fin n→HeatCircle)
    (hσ:∀i,0<σ i)(hσ1:∀i,σ i≤1)(hages:∀i,σ i≤target i)
    (lo hi:Fin r→ℝ)(hlo:∀j,0≤lo j)(hgap:∀j,lo j<hi j)(hstop:∀j i,σ i≤lo j ∨ hi j≤σ i)
    (c:Domain→ℝ)(hc:Measurable c){ell M:ℝ}(hell:0<ell)(hcb:∀p,ell≤c p ∧ c p≤M)(p:ℕ):
    ∀ᵐx:Fin r→HeatCircle ∂Measure.pi (fun _:Fin r=>haarAddCircle),
      let A:=familyCovariance σ target center c lo hi
      let D:=familyDirection σ target center lo x
      Integrable (fun y:Fin r→State n=>|∏j,secondScore (A j) (D j) (y j)|^(2*p))
        (Measure.pi (fun j=>multivariateGaussian 0 (A j))) ∧
      (∫y:Fin r→State n,|∏j,secondScore (A j) (D j) (y j)|^(2*p)
        ∂Measure.pi (fun j=>multivariateGaussian 0 (A j)))=
        (secondScoreMoment p)^r*(∏j,scoreVariance (A j) (D j))^(2*p):=by
  filter_upwards[family_directions_mem_range_ae σ target center hσ hσ1 hages lo hi hlo hgap hstop c hc hell hcb]
    with x hx
  exact product_even_moment _ (fun j=>covariance_posSemidef σ target center hages c hc
    (fun z=>⟨hell.le.trans (hcb z).1,(hcb z).2⟩) (lo j) (hi j)) _ hx p

end SHE.OldIntervalScoreMoments
