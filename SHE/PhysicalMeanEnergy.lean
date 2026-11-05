module

public import SHE.PhysicalMeanRange
public import SHE.GaussianScoreQuadratic

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.PhysicalMeanEnergy
open Set MeasureTheory AddCircle Real StoppedFourier StoppedGaussianFeatures StoppedGaussianScore
  GaussianIncrement MeasurableGaussianScores MeasurableGeneralizedInverse PhysicalMeanRange
  StoppedMeanRange StoppedMeanEnergy HeatProjection
open scoped InnerProductSpace
local instance physicalMeanEnergy_periodPos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {n : ℕ}

theorem covariance_positive (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (q : ℝ)
    (hages : ∀ i, σ i ≤ target i) (c : Domain → ℝ) (hc : Measurable c) (U : ℝ)
    (hcb : ∀ p, 0 ≤ c p ∧ c p ≤ U) :
    (stoppedCovariance σ target (nativeCenter a) c q).PosSemidef := by
  rw [← weightedFeature_gram σ target (nativeCenter a) c hc U hcb hages q]
  exact Matrix.posSemidef_gram ℝ _

theorem current_score_bound (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (q : ℝ)
    (hages : ∀ i, σ i ≤ target i) (δ : ℝ) (hδ : 0 < δ) (hstop : ∀ i, q + δ ≤ σ i)
    (c : Domain → ℝ) (hc : Measurable c) (U ell : ℝ)
    (hcb : ∀ p, 0 ≤ c p ∧ c p ≤ U) (hell : 0 < ell) (hcl : ∀ p, ell ≤ c p)
    (d : CircleL2) :
    scoreVariance (stoppedCovariance σ target (nativeCenter a) c q) (currentDirection target a q d) ≤
      ((2 / δ) / ell) * ‖d‖ ^ 2 := by
  let t : Fin n → ℝ := fun i => (target i - q) / (4 * π ^ 2)
  have ht : ∀ i, 0 < t i := fun i => div_pos (by linarith [hstop i, hages i]) (by positivity)
  have he : ∀ i, target i - q = 4 * π ^ 2 * t i := by intro i; dsimp [t]; field_simp
  have ha : ∀ i, q < σ i := fun i => by linarith [hstop i]
  rw [currentDirection_eq σ target a q t ht he ha d]
  have hh := (current_mean_range σ target a q t he hages δ hδ hstop c hc U ell hcb hell hcl
    (CircleNormalization.push.symm d)).2
  have hn := pow_le_pow_left₀ (norm_nonneg _) ((heatSpan t a).norm_starProjection_apply_le (CircleNormalization.push.symm d)) 2
  rw [CircleNormalization.push.symm.norm_map] at hn
  exact hh.trans (mul_le_mul_of_nonneg_left hn (by positivity))

theorem damped_score_bound (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (q Λ : ℝ)
    (hΛ : 0 ≤ Λ) (hages : ∀ i, σ i ≤ target i) (δ : ℝ) (hδ : 0 < δ) (hstop : ∀ i, q + δ ≤ σ i)
    (c : Domain → ℝ) (hc : Measurable c) (U ell : ℝ)
    (hcb : ∀ p, 0 ≤ c p ∧ c p ≤ U) (hell : 0 < ell) (hcl : ∀ p, ell ≤ c p)
    (d : CircleL2) :
    scoreVariance (stoppedCovariance σ target (nativeCenter a) c q) (dampedDirection σ target a q Λ d) ≤
      ((2 / δ) / ell) * ‖d‖ ^ 2 := by
  by_cases h0 : Λ = 0
  · simpa only [h0, dampedDirection, currentDirection, neg_zero, zero_mul, exp_zero, one_mul] using
      current_score_bound σ target a q hages δ hδ hstop c hc U ell hcb hell hcl d
  let t : Fin n → ℝ := fun i => (target i - q) / (4 * π ^ 2)
  have ht : ∀ i, 0 < t i := fun i => div_pos (by linarith [hstop i, hages i]) (by positivity)
  have he : ∀ i, target i - q = 4 * π ^ 2 * t i := by intro i; dsimp [t]; field_simp
  have ha : ∀ i, q < σ i := fun i => by linarith [hstop i]
  rw [dampedDirection_eq σ target a q Λ t ht he ha d]
  have hh := (damped_mean_range σ target a q Λ (lt_of_le_of_ne hΛ (Ne.symm h0)) t he hages δ hδ hstop c hc U ell hcb hell hcl
    (CircleNormalization.push.symm d)).2
  have hn := pow_le_pow_left₀ (norm_nonneg _) ((heatSpan t a).norm_starProjection_apply_le (CircleNormalization.push.symm d)) 2
  rw [CircleNormalization.push.symm.norm_map] at hn
  exact hh.trans (mul_le_mul_of_nonneg_left hn (by positivity))

theorem currentDirection_measurable {X : Type*} [MeasurableSpace X]
    (target : Fin n → ℝ) (a : X → Fin n → UnitAddCircle) (ha : ∀ i, Measurable (fun x => a x i))
    (q : ℝ) (d : CircleL2) : Measurable (fun x => currentDirection target (a x) q d) := by
  apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
  apply Measurable.of_eval
  intro i
  exact (PhysicalProfile.physicalHeatMean_measurable d).comp
    (measurable_const.prodMk ((CircleNormalization.continuous_scale 1 (2 * π)).measurable.comp (ha i)))

theorem dampedDirection_measurable {X : Type*} [MeasurableSpace X]
    (σ target : Fin n → ℝ) (a : X → Fin n → UnitAddCircle) (ha : ∀ i, Measurable (fun x => a x i))
    (q Λ : ℝ) (d : CircleL2) : Measurable (fun x => dampedDirection σ target (a x) q Λ d) := by
  apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
  apply Measurable.of_eval
  intro i
  exact ((PhysicalProfile.physicalHeatMean_measurable d).comp
    (measurable_const.prodMk ((CircleNormalization.continuous_scale 1 (2 * π)).measurable.comp (ha i)))).const_mul _

theorem dampedDirection_continuous_lambda (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle)
    (q : ℝ) (d : CircleL2) : Continuous (fun Λ => dampedDirection σ target a q Λ d) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
  apply continuous_pi
  intro i
  change Continuous (fun Λ : ℝ => exp (-Λ * (σ i - q)) * PhysicalProfile.physicalHeatMean d (target i - q, nativeCenter a i))
  fun_prop

theorem scoreVariance_continuous_direction (A : Mat n) : Continuous (scoreVariance A) := by
  exact ((generalizedInverse A).toContinuousLinearMap.continuous).inner continuous_id

end SHE.PhysicalMeanEnergy
