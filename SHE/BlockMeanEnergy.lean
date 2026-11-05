module

public import SHE.GaussianBlockFrame

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

/-! Actual canonical real Gaussian mean energy for finitely many comparable
age blocks. The original full covariance stays in the score, and each
block retains its genuine signed-input heat factor. -/
namespace SHE.BlockMeanEnergy
open Set MeasureTheory AddCircle Real HeatTorus HeatProjection GaussianIncrement
  GaussianGramScore MeasurableGaussianScores RealHeatCovarianceMean GaussianBlockFrame
open scoped InnerProductSpace

theorem translated_block_scoreVariance_bound (q : ℕ) :
    ∃ h K θ : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < K ∧ 0 < θ ∧
      ∀ {g n : ℕ} (t : Fin g → Fin q → ℝ) (a : Fin g → Fin q → UnitAddCircle),
      (∀ j i, 0 < t j i) → (∀ j i, t j i ≤ h) →
      ∀ (w M : Fin g → ℝ), (∀ j, 0 < w j) → (∀ j, 1 ≤ M j) →
      (∀ j i, w j ≤ t j i) → (∀ j i, t j i ≤ M j * w j) →
      ∀ {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
      (v : UnitAddCircle → Fin n → H) (C : Fin g → UnitAddCircle → State n →ₗ[ℝ] G)
      (S : Fin g → UnitAddCircle → State n →ₗ[ℝ] CircleL2),
      Measurable (fun x => Matrix.gram ℝ (v x)) →
      (∀ j i, StronglyMeasurable (fun x => S j x (EuclideanSpace.basisFun (Fin n) ℝ i))) →
      ∀ (L : Fin g → ℝ) (c : ℝ), (∀ j, 0 ≤ L j) → 0 < c →
      (∀ j x z, S j x z ∈ heatSpan (t j) (fun i => a j i + x)) →
      (∀ j x z, ‖S j x z‖ ≤ L j * ‖C j x z‖) →
      (∀ x z, c * (∑ j, ‖C j x z‖ ^ 2) ≤ ‖featureSynthesis (v x) z‖ ^ 2) →
      ∀ d : CircleL2,
      Integrable (fun x => scoreVariance (Matrix.gram ℝ (v x))
        (meanDirection (∑ j, S j x) d)) haarAddCircle ∧
      (∫ x, scoreVariance (Matrix.gram ℝ (v x)) (meanDirection (∑ j, S j x) d) ∂haarAddCircle) ≤
        (K / c) * ∑ j, L j ^ 2 * sqrt (M j) * sqrt (w j) * ‖CircleHeat.heat (θ * w j) d‖ ^ 2 := by
  obtain ⟨h, K, θ, hh, hh1, hK, hθ, hproj⟩ := translated_heat_span_projection_bound q
  refine ⟨h, K, θ, hh, hh1, hK, hθ, ?_⟩
  intro g n t a ht hth w M hw hM hlo hhi H G _ _ _ _ _ _ v C S hcov hS L c hL hc hspan hbound hframe d
  have hpi (j : Fin g) := hproj (t j) (a j) (ht j) (hth j) (w j) (M j)
    (hw j) (hM j) (hlo j) (hhi j) d
  have hSm (i : Fin n) : StronglyMeasurable
      (fun x => (∑ j, S j x) (EuclideanSpace.basisFun (Fin n) ℝ i)) := by
    convert! Finset.stronglyMeasurable_sum Finset.univ (fun j _ => hS j i) using 1
    funext x
    simp only [LinearMap.sum_apply, Finset.sum_apply]
  have hm : Measurable (fun x => scoreVariance (Matrix.gram ℝ (v x))
      (meanDirection (∑ j, S j x) d)) := by
    convert! scoreVariance_measurable.comp
      (hcov.prodMk (meanDirection_measurable (fun x => ∑ j, S j x) hSm d)) using 1
  have hpt (x : UnitAddCircle) := block_scoreVariance_projection_bound t
    (fun j i => a j i + x) (v x) (fun j => C j x) (fun j => S j x) L hL
    (fun j z => hspan j x z) (fun j z => hbound j x z) hc (hframe x) d
  have hdom : Integrable (fun x =>
      (∑ j, L j ^ 2 * ‖(heatSpan (t j) (fun i => a j i + x)).starProjection d‖ ^ 2) / c) haarAddCircle := by
    exact (integrable_finsetSum Finset.univ (fun j _ => (hpi j).1.const_mul (L j ^ 2))).div_const c
  have hi : Integrable (fun x => scoreVariance (Matrix.gram ℝ (v x))
      (meanDirection (∑ j, S j x) d)) haarAddCircle := by
    apply hdom.mono' hm.aestronglyMeasurable
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg
      (scoreVariance_nonneg (Matrix.posSemidef_gram ℝ (v x)) (hpt x).1)]
    exact (hpt x).2
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, (∑ j, L j ^ 2 * ‖(heatSpan (t j) (fun i => a j i + x)).starProjection d‖ ^ 2) / c
        ∂haarAddCircle := integral_mono hi hdom (fun x => (hpt x).2)
    _ = (∑ j, L j ^ 2 * (∫ x,
        ‖(heatSpan (t j) (fun i => a j i + x)).starProjection d‖ ^ 2 ∂haarAddCircle)) / c := by
      rw [integral_div, integral_finsetSum Finset.univ (fun j _ => (hpi j).1.const_mul (L j ^ 2))]
      simp_rw [integral_const_mul]
    _ ≤ (∑ j, L j ^ 2 * (K * sqrt (M j) * sqrt (w j) * ‖CircleHeat.heat (θ * w j) d‖ ^ 2)) / c := by
      apply div_le_div_of_nonneg_right _ hc.le
      exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hpi j).2 (sq_nonneg _))
    _ = _ := by
      rw [Finset.mul_sum, Finset.sum_div]
      exact Finset.sum_congr rfl (fun j _ => by ring)

end SHE.BlockMeanEnergy
