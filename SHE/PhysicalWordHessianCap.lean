module

public import SHE.FixedOldHessianBound
public import SHE.FullResidualChainAverage
public import SHE.PredictablePhysicalFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2500000
noncomputable section

namespace SHE.PhysicalChainArrays
open Set Filter MeasureTheory ProbabilityTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open CutoffCarriers PhysicalScoreChain OldIntervalCovariance StoppedGaussianFeatures GaussianConvolution
open MeasurableGaussianScores SmoothCylinders
open scoped BigOperators
local instance physicalWordHessianCap_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] fullResidualCovariance oldAverage WordRecursion.covariance
  MeasurableGaussianScores.scoreVariance MeasurableGeneralizedInverse.generalizedInverse
  WordRecursion.directionalSecond GaussianConvolution.gaussianAverage UncutSmoothWords.test
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : Level R X n)

/-- A genuine directional Hessian cap for EVERY actual finite-depth
recursive word. The only coefficient inputs are its common zeroth-order
cap and ellipticity. All coefficient derivatives have been transferred
to the genuine Gaussian second score. -/
theorem actual_hessian_cap_ae (c : Domain→ℝ) (hc : Measurable c)
    {ell A B : ℝ} (hell : 0<ell) (hb : ∀p,ell≤c p ∧ c p≤R.reference p)
    (hA : 0≤A) (hB : 0≤B) (ha : ∀z,|R.totalVariance z|≤A)
    (hroot : ∀p z,|L.test p z|≤B)
    (hages : ∀p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (μ : Measure X) [IsFiniteMeasure μ] (k : ℕ) :
    ∀ᵐ p∂CutoffWordHistories.historyMeasure R μ k,
      ∀q:ℝ,0≤q→q<(carrier L k).terminal p→
      ∀d z:WordRecursion.State (n+k),
        d∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (fullResidualCovariance L c k p q)).range→
        |WordRecursion.directionalSecond
          (gaussianAverage (WordRecursion.covariance R.reference
            ((carrier L k).observations.observations p) q ((carrier L k).terminal p))
              (UncutSmoothWords.test L k p)) z d|≤
          2*((B*((A+R.upper)/2)^k)*oldAbsoluteMass L c k p)*
            scoreVariance (fullResidualCovariance L c k p q) d := by
  filter_upwards [exists_chain_ae L c hc hell hb hages μ k,
    full_residual_first_score_ae L c hc hell hb hages μ k] with p hp hs
  obtain ⟨chain,hchain,_,hphysical⟩:=hp
  intro q hq hqt d z hd
  have hZ:=RecursiveScoreSupport.carrier_ages L hages k p
  have hrep:=funext (full_residual_average_of_chain L c chain hchain hphysical hZ q hq hqt.le)
  have hF:=RecursiveGaussianScores.test_boundedSmooth L k p
  have hG:Measurable (oldAverage L c k p):=
    (oldAverage_measurable L c hc k).comp (measurable_const.prodMk measurable_id)
  have hcap:=oldAverage_cap L c hA hB ha hroot k p
  have hM:0≤(B*((A+R.upper)/2)^k)*oldAbsoluteMass L c k p:=mul_nonneg
    (mul_nonneg hB (pow_nonneg (div_nonneg (add_nonneg hA R.upper_nonneg) (by norm_num)) _))
      (oldAbsoluteMass_nonneg L c k p)
  exact FixedOldHessianBound.hessian_bound (hs q hq hqt).1 hd hF hG _ hM hcap hrep z

end SHE.PhysicalChainArrays
