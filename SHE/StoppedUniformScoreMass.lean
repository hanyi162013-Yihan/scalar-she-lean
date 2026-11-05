module

public import SHE.FullResidualFrameRange

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.StoppedUniformScoreMass
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier StoppedGaussianFeatures
  StoppedScoreLeverage MeasurableGaussianScores GaussianIncrement GaussianProfileMark GaussianGramScore
open scoped BigOperators InnerProductSpace
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {n : ℕ}
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse

/-- The reference leverage has at most the original observation count
as its mass at every lower cutoff, including inactive terminal coordinates. -/
theorem reference_mass (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (q : ℝ) :
    Integrable (referenceKernel σ target center hages q) (historyMeasure q) ∧
      (∫ p, referenceKernel σ target center hages q p ∂historyMeasure q) ≤ (n : ℝ) := by
  let v := referenceFeature σ target center hages q
  have hi (k : FrameIndex v) : Integrable
      (fun p => (inner ℝ (frameCoefficients v k) (stoppedRow σ target center p)) ^ 2)
        (historyMeasure q) := by
    simpa only [realHistory_eq_inner] using
      realHistory_square_product_integrable σ target center hages (frameCoefficients v k) q
  have hm (k : FrameIndex v) :
      (∫ p, (inner ℝ (frameCoefficients v k) (stoppedRow σ target center p)) ^ 2
        ∂historyMeasure q) = 1 := by
    have hn := weightedSynthesis_norm_sq σ target center (fun _ => 1) measurable_const 1
      (fun _ => ⟨zero_le_one, le_rfl⟩) hages q (frameCoefficients v k)
    simp only [one_mul, realHistory_eq_inner] at hn
    change ‖featureSynthesis v (frameCoefficients v k)‖ ^ 2 = _ at hn
    rw [← hn, (frameCoefficients_orthonormal v).norm_eq_one k, one_pow]
  have he : referenceKernel σ target center hages q =
      fun p => ∑ k : FrameIndex v,
        (inner ℝ (frameCoefficients v k) (stoppedRow σ target center p)) ^ 2 :=
    funext (referenceKernel_eq σ target center hages q)
  rw [he]
  refine ⟨integrable_finsetSum _ (fun k _ => hi k), ?_⟩
  rw [integral_finsetSum _ (fun k _ => hi k)]
  simp only [hm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact_mod_cast frame_card_le v

/-- Uniform bounded signed-input mass under any elliptic stopped law.
There is no smallest positive future-age hypothesis or matrix inverse
conditioning constant in the bound. -/
theorem bounded_input (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (q : ℝ) (c : Domain → ℝ) (hc : Measurable c)
    {ell M : ℝ} (hell : 0 < ell) (hcb : ∀ p, ell ≤ c p ∧ c p ≤ M)
    (e : Domain → ℝ) (he : Measurable e) {E : ℝ} (hE : 0 ≤ E) (hb : ∀ p, |e p| ≤ E) :
    Integrable (fun p => |e p| * scoreVariance (stoppedCovariance σ target center c q)
      (stoppedRow σ target center p)) (historyMeasure q) ∧
    (∫ p, |e p| * scoreVariance (stoppedCovariance σ target center c q)
      (stoppedRow σ target center p) ∂historyMeasure q) ≤ E * (n : ℝ) / ell := by
  have hB := StoppedCovarianceSplit.covariance_posSemidef σ target center hages q hc
    (fun p => ⟨hell.le.trans (hcb p).1, (hcb p).2⟩)
  have hr := FullResidualFrameRange.row_mem_all_ranges_ae σ target center hages q
    (fun _ : Unit => c) (fun _ => hc) hell (fun _ => hcb)
  have hs := score_le_reference_ae σ target center hages c hc M
    (fun p => ⟨hell.le.trans (hcb p).1, (hcb p).2⟩) hell (fun p => (hcb p).1) q
  have hk := reference_mass σ target center hages q
  have hk0 (p) : 0 ≤ referenceKernel σ target center hages q p := by
    rw [referenceKernel_eq]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hbound : ∀ᵐ p ∂historyMeasure q,
      ‖|e p| * scoreVariance (stoppedCovariance σ target center c q)
          (stoppedRow σ target center p)‖ ≤
        (E / ell) * referenceKernel σ target center hages q p := by
    filter_upwards [hr, hs] with p hp hs
    have hv := scoreVariance_nonneg hB (hp ())
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hv)]
    calc
      _ ≤ |e p| * (referenceKernel σ target center hages q p / ell) :=
        mul_le_mul_of_nonneg_left hs (abs_nonneg _)
      _ ≤ E * (referenceKernel σ target center hages q p / ell) :=
        mul_le_mul_of_nonneg_right (hb p) (div_nonneg (hk0 p) hell.le)
      _ = _ := by ring
  have hm : Measurable (fun p => |e p| * scoreVariance
      (stoppedCovariance σ target center c q) (stoppedRow σ target center p)) :=
    (continuous_abs.measurable.comp he).mul
      (scoreVariance_measurable.comp
        (measurable_const.prodMk (stoppedRow_measurable σ target center)))
  have hi := (hk.1.const_mul (E / ell)).mono' hm.aestronglyMeasurable hbound
  refine ⟨hi, ?_⟩
  have hh := (integral_mono_ae hi (hk.1.const_mul (E / ell))
    (hbound.mono (fun p hp => (le_abs_self _).trans hp))).trans_eq
      (integral_const_mul (E / ell) _)
  exact hh.trans ((mul_le_mul_of_nonneg_left hk.2 (div_nonneg hE hell.le)).trans_eq (by ring))

end SHE.StoppedUniformScoreMass
