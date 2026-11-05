module

public import SHE.GramScoreDomination
public import SHE.PositiveMatrixRanges
public import SHE.StoppedCovarianceSplit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.StoppedCovarianceOrder
open Set MeasureTheory Real GaussianIncrement GaussianGramScore StoppedFourier
  StoppedGaussianFeatures MeasurableGaussianScores
open scoped InnerProductSpace
local instance : Fact (0<2*π) := ⟨by positivity⟩
variable {n : ℕ}

/-- Genuine covariance order for the literal individually stopped rows.
The positive difference is an actual covariance of a nonnegative profile. -/
theorem covariance_sub_posSemidef (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hages : ∀ i,σ i≤target i) (q : ℝ) (c d : Domain→ℝ) (hc : Measurable c) (hd : Measurable d)
    {M N : ℝ} (hcb : ∀ p,0≤c p ∧ c p≤M) (hdb : ∀ p,0≤d p ∧ d p≤N)
    (hcd : ∀ p,c p≤d p) :
    (stoppedCovariance σ target center d q-stoppedCovariance σ target center c q).PosSemidef := by
  rw [←StoppedCovarianceSplit.covariance_sub σ target center hages q hd hc
    (fun p => (abs_of_nonneg (hdb p).1).trans_le (hdb p).2)
    (fun p => (abs_of_nonneg (hcb p).1).trans_le (hcb p).2)]
  exact StoppedCovarianceSplit.covariance_posSemidef σ target center hages q (hd.sub hc)
    (fun p => ⟨sub_nonneg.mpr (hcd p),(sub_le_self _ (hcb p).1).trans (hdb p).2⟩)

theorem range_mono (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hages : ∀ i,σ i≤target i) (q : ℝ) (c d : Domain→ℝ) (hc : Measurable c) (hd : Measurable d)
    {M N : ℝ} (hcb : ∀ p,0≤c p ∧ c p≤M) (hdb : ∀ p,0≤d p ∧ d p≤N)
    (hcd : ∀ p,c p≤d p) :
    (Matrix.toEuclideanCLM (𝕜:=ℝ) (stoppedCovariance σ target center c q)).range≤
      (Matrix.toEuclideanCLM (𝕜:=ℝ) (stoppedCovariance σ target center d q)).range := by
  apply PositiveMatrixRanges.range_le_of_domination
    (StoppedCovarianceSplit.covariance_posSemidef σ target center hages q hd hdb)
    (StoppedCovarianceSplit.covariance_posSemidef σ target center hages q hc hcb) 1
  simpa only [one_smul] using covariance_sub_posSemidef σ target center hages q c d hc hd hcb hdb hcd

/-- Canonical score variance decreases under actual physical covariance
domination, including singular matrices. The proof compares the real
weighted Gaussian feature energies, not matrix inverse entries. -/
theorem scoreVariance_antitone (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hages : ∀ i,σ i≤target i) (q : ℝ) (c d : Domain→ℝ) (hc : Measurable c) (hd : Measurable d)
    {M N : ℝ} (hcb : ∀ p,0≤c p ∧ c p≤M) (hdb : ∀ p,0≤d p ∧ d p≤N)
    (hcd : ∀ p,c p≤d p) {direction : State n}
    (hrange : direction∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (stoppedCovariance σ target center c q)).range) :
    scoreVariance (stoppedCovariance σ target center d q) direction≤
      scoreVariance (stoppedCovariance σ target center c q) direction := by
  let v := weightedFeature σ target center c hc M hcb hages q
  let w := weightedFeature σ target center d hd N hdb hages q
  have hdom (z : State n) : (1:ℝ)*‖featureSynthesis v z‖^2≤‖featureSynthesis w z‖^2 := by
    rw [one_mul,weightedSynthesis_norm_sq σ target center c hc M hcb hages q z,
      weightedSynthesis_norm_sq σ target center d hd N hdb hages q z]
    exact integral_mono (weightedHistory_integrable σ target center c hc M hcb hages q z)
      (weightedHistory_integrable σ target center d hd N hdb hages q z)
      (fun p => mul_le_mul_of_nonneg_right (hcd p) (sq_nonneg _))
  have hr : direction∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (Matrix.gram ℝ v)).range := by
    simpa only [v,weightedFeature_gram] using hrange
  have hh := scoreVariance_le_of_gram_domination v w (by norm_num : 0<(1:ℝ)) hdom hr
  simpa only [v,w,weightedFeature_gram,div_one] using hh

end SHE.StoppedCovarianceOrder
