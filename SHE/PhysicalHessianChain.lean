module
public import SHE.PhysicalFreshRowMass
public import SHE.PhysicalOldHolder
public import SHE.MatrixHolderScore
public import SHE.FixedOldAbsoluteMass

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2300000
namespace SHE.PhysicalChainArrays
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalScoreChain ProjectedUncutWord GaussianConvolution MeasurableGaussianScores
  StoppedGaussianFeatures GaussianAudit SmoothCylinders
open scoped BigOperators
local instance physicalHessianChain_period : Fact (0<2*Real.pi):=⟨by positivity⟩
attribute [local irreducible] fullResidualCovariance oldAverage WordRecursion.covariance
  WordRecursion.directionalSecond GaussianConvolution.gaussianAverage UncutSmoothWords.test
variable {X:Type} [MeasurableSpace X] {R:ReferenceData} {n:ℕ} (L:Level R X n)

theorem old_absolute_mass_of_chain (c:Domain→ℝ)(k:ℕ)(p:History X k)
    (chain:Chain L k p (fun i=>i))
    (hp:Physical L ((carrier L k).observations.observations p) c chain):
    oldAbsoluteMass L c k p≤(2:ℝ)^k*
      scoreProduct L ((carrier L k).observations.observations p) c k p := by
  have hh:=product_score_absolute_mass chain.old chain.old_posSemidef chain.direction
    (SHE.PhysicalChainArrays.Chain.fixed_direction_mem_range L chain)
  rw [Physical.old_eq L _ c chain hp,Physical.direction_eq L _ c chain hp] at hh
  exact hh

/-- Pointwise in the physical chain, hence usable on a common
all-parameter chain event before random-past substitution. -/
theorem hessian_second_score_of_chain (c:Domain→ℝ)(hc:Measurable c)
    {ell:ℝ}(hell:0<ell)(hR:∀p,ell≤R.reference p)
    (hages:∀p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (k:ℕ)(p:History X k)(chain:Chain L k p (fun i=>i))(hs:chain.CoordinateSupport)
    (hp:Physical L ((carrier L k).observations.observations p) c chain)
    (q:ℝ)(hq:0≤q)(hqt:q<(carrier L k).terminal p)
    (d z:WordRecursion.State (n+k))
    (hd:d∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (fullResidualCovariance L c k p q)).range):
    WordRecursion.directionalSecond
      (gaussianAverage (WordRecursion.covariance R.reference
        ((carrier L k).observations.observations p) q ((carrier L k).terminal p))
          (UncutSmoothWords.test L k p)) z d=
      ∫y,oldAverage L c k p (z+y)*secondScore (fullResidualCovariance L c k p q) d y
        ∂multivariateGaussian 0 (fullResidualCovariance L c k p q) := by
  have hT := (fresh_row_score_mass_of_chain L c hell hR hages k p chain hp q hq hqt).1
  have hrep:=funext (full_residual_average_of_chain L c chain hs hp
    (RecursiveScoreSupport.carrier_ages L hages k p) q hq hqt.le)
  have hF:=RecursiveGaussianScores.test_boundedSmooth L k p
  have hG:Measurable (oldAverage L c k p):=
    (oldAverage_measurable L c hc k).comp (measurable_const.prodMk measurable_id)
  obtain ⟨B,_,hB⟩:=oldAverage_bounded L c k p
  exact FixedOldHessianBound.hessian_eq_secondScore hT hd hF hG B hB hrep z

/-- The actual fresh Hölder estimate is pointwise in a supplied true
physical chain. Its constant uses no coefficient derivatives, and the
same event can therefore serve every random past input and theta. -/
theorem hessian_holder_of_chain (c:Domain→ℝ)(hc:Measurable c)
    {ell A B H K β:ℝ}(hell:0<ell)(hR:∀p,ell≤R.reference p)
    (hA:0≤A)(hB:0≤B)(hH:0≤H)(hK:0≤K)(hβ:0≤β)
    (ha:∀z,|R.totalVariance z|≤A)(hroot:∀p z,|L.test p z|≤B)
    (hh:∀s t,|R.totalVariance s-R.totalVariance t|≤H*|s-t|^β)
    (hages:∀p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (k:ℕ)(p:History X k)(chain:Chain L k p (fun i=>i))(hs:chain.CoordinateSupport)
    (hp:Physical L ((carrier L k).observations.observations p) c chain)
    (q:ℝ)(hq:0≤q)(hqt:q<(carrier L k).terminal p)
    (d z:WordRecursion.State (n+k))
    (hd:d∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (fullResidualCovariance L c k p q)).range)
    (hrootmod:∀x s t,|initial L k p (fun i=>i) (x+s•d)-initial L k p (fun i=>i) (x+t•d)|≤K*|s-t|^β):
    |WordRecursion.directionalSecond
      (gaussianAverage (WordRecursion.covariance R.reference
        ((carrier L k).observations.observations p) q ((carrier L k).terminal p))
          (UncutSmoothWords.test L k p)) z d|≤
      (wordHolderCost (R:=R) A B H K β k p d*oldAbsoluteMass L c k p)*
        secondScoreAbsIncrementMoment β*scoreVariance (fullResidualCovariance L c k p q) d^(1-β/2) := by
  rw [hessian_second_score_of_chain L c hc hell hR hages k p chain hs hp q hq hqt d z hd]
  have hT := (fresh_row_score_mass_of_chain L c hell hR hages k p chain hp q hq hqt).1
  have hG:Measurable (oldAverage L c k p):=
    (oldAverage_measurable L c hc k).comp (measurable_const.prodMk measurable_id)
  exact MatrixHolderScore.integral_bound hT hd hG (oldAverage_cap L c hA hB ha hroot k p)
    (mul_nonneg (wordHolderCost_nonneg hA hB hH hK k p d) (oldAbsoluteMass_nonneg L c k p)) hβ
    (oldAverage_directional_holder L c hA hB hH hK ha hroot hh k p d hrootmod) z

end SHE.PhysicalChainArrays
