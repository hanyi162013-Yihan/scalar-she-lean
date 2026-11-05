module

public import SHE.PredictableChainCovariance

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.PhysicalScoreChain
open Set Filter MeasureTheory ProbabilityTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open CutoffCarriers ProjectedUncutWord GaussianConvolution GaussianCoordinates
open scoped BigOperators
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

/-- The actual reserved covariance is positive because it is the sum of
the true initial covariance and all actual residual interval covariances. -/
theorem Physical.reserved_posSemidef {k : ℕ} {p : History P k}
    (hZ : ∀ i, ((carrier L k).observations.observations p i).stop ≤
      ((carrier L k).observations.observations p i).target)
    (c : StoppedGaussianFeatures.Domain → ℝ) (hc : Measurable c) {ell : ℝ} (hell : 0 < ell)
    (hb : ∀ z, ell ≤ c z ∧ c z ≤ R.reference z)
    (chain : Chain (N := n+k) L k p (fun i => i))
    (hp : Physical L ((carrier L k).observations.observations p) c chain) :
    (windowCovariance L k p - ∑ j, chain.old j).PosSemidef := by
  rw [← hp.residual_covariance L hZ c hc hell hb chain]
  exact ((carrier L k).nodeCovariance (p,(R.base,0))).property.add
    (Matrix.posSemidef_sum _ (fun j _ => chain.residual_posSemidef j))

/-- Exact all-order physical predictable representation at every mean,
for almost every genuine original history. All chain applicability and
triangular-support conditions are conclusions of the physical construction. -/
theorem predictable_representation_ae (c : StoppedGaussianFeatures.Domain → ℝ)
    (hc : Measurable c) {ell : ℝ} (hell : 0 < ell)
    (hb : ∀ z, ell ≤ c z ∧ c z ≤ R.reference z)
    (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (μ : Measure P) [IsFiniteMeasure μ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure R μ k,
      ∃ chain : Chain (N := n+k) L k p (fun i => i),
        chain.CoordinateSupport ∧ Physical L ((carrier L k).observations.observations p) c chain ∧
        (windowCovariance L k p - ∑ j, chain.old j).PosSemidef ∧
        ∀ z : WordRecursion.State (n+k),
          gaussianAverage (initialCovariance L k p) (UncutSmoothWords.test L k p) z =
            gaussianAverage (windowCovariance L k p - ∑ j, chain.old j) chain.oldAverage z := by
  filter_upwards [exists_chain_ae L c hc hell hb hages μ k] with p hp
  obtain ⟨chain,hs,_,hphysical⟩ := hp
  have hZ := RecursiveScoreSupport.carrier_ages L hages k p
  refine ⟨chain,hs,hphysical,hphysical.reserved_posSemidef L hZ c hc hell hb chain,?_⟩
  intro z
  have h := chain.predictable_eq_reserved_average hs
    ((carrier L k).nodeCovariance (p,(R.base,0))).property z
  have hid : projection (fun i : Fin (n+k) => i) =
      ContinuousLinearMap.id ℝ (WordRecursion.State (n+k)) := by ext x i; rfl
  simp only [hid,ContinuousLinearMap.id_apply] at h
  change gaussianAverage (initialCovariance L k p) (UncutSmoothWords.test L k p) z =
    gaussianAverage (initialCovariance L k p + ∑ j, chain.residual j) chain.oldAverage z at h
  rw [hphysical.residual_covariance L hZ c hc hell hb chain] at h
  exact h

end SHE.PhysicalScoreChain
