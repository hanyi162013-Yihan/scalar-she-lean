module

public import SHE.IntervalScoreMass
public import SHE.StoppedHeatSpanEnvelope

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.IntervalScoreEnvelope
open Set Filter MeasureTheory ProbabilityTheory AddCircle GaussianIncrement StoppedGaussianFeatures
  StoppedFourier OldIntervalCovariance GaussianGramScore MeasurableGaussianScores GaussianProfileMark IntervalScoreMass
open scoped BigOperators InnerProductSpace
local instance intervalScoreEnvelope_periodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The actual canonical second-score scale has the original positive
spatial Gaussian envelope, divided by the true old interval length. Only
original active observations enter its parent sum. All collisions and
singular covariance ranks are permitted. -/
theorem score_envelope (n : ℕ) :
    ∃ H C : ℝ, 0 < H ∧ 0 < C ∧
      ∀ (σ target : Fin n → ℝ) (center : Fin n → HeatCircle),
      (∀ i, σ i ≤ target i) → ∀ {lo hi ell M : ℝ},
      0 ≤ lo → lo < hi → (∀ i, σ i ≤ lo ∨ hi ≤ σ i) →
      (∀ i, hi ≤ σ i → target i - lo ≤ H) →
      ∀ (c : Domain → ℝ), Measurable c → 0 < ell → (∀ p, ell ≤ c p ∧ c p ≤ M) →
      ∀ᵐ x : HeatCircle ∂haarAddCircle,
        scoreVariance (StoppedGaussianFeatures.stoppedCovariance σ target center (intervalProfile c lo hi) 0)
          (StoppedGaussianFeatures.stoppedRow σ target center (lo,x)) ≤
          (C / (ell * (hi-lo))) * StoppedHeatSpanEnvelope.weight σ target center lo hi x := by
  obtain ⟨H, C, hH, hC, henv⟩ := StoppedHeatSpanEnvelope.stopped_heat_span_envelope n
  refine ⟨H, ((n:ℝ)+1)*C, hH, by positivity, ?_⟩
  intro σ target center hages lo hi ell M hlo hgap hstop hsmall c hc hell hb
  let v := feature σ target center hages c hc M (fun p => ⟨hell.le.trans (hb p).1, (hb p).2⟩) lo hi
  let a := frameCoefficients v
  have hden : 0 < ell * (hi-lo) := mul_pos hell (sub_pos.mpr hgap)
  have hgram : Matrix.gram ℝ v =
      StoppedGaussianFeatures.stoppedCovariance σ target center (intervalProfile c lo hi) 0 :=
    feature_gram σ target center hages c hc M (fun p => ⟨hell.le.trans (hb p).1, (hb p).2⟩) lo hi
  have hrow := endpoint_row_mem_range_unrestricted σ target center hages hlo hgap hstop c hc hell hb
  have hn (j : FrameIndex v) : ‖historyF Finset.univ (fun i => (a j i : ℂ)) σ target center lo‖ ^ 2 ≤
      (ell*(hi-lo))⁻¹ := by
    have hh : ell*(hi-lo)*(∫ x, realHistory σ target center (a j) (lo,x)^2 ∂haarAddCircle) ≤
        ‖featureSynthesis v (a j)‖^2 := endpoint_domination σ target center hages c hc hlo hgap hstop hell hb (a j)
    rw [(frameCoefficients_orthonormal v).norm_eq_one j, one_pow,
      realHistory_square_mass σ target center hages] at hh
    rw [inv_eq_one_div, le_div_iff₀ hden]
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hh
  have hE (j : FrameIndex v) := henv σ target center hages hgap hstop hsmall (fun i => (a j i : ℂ))
  have hR (j : FrameIndex v) := realHistory_square_ae σ target center hages (a j) lo
  filter_upwards [hrow, ae_all_iff.mpr hE, ae_all_iff.mpr hR] with x hx hEx hRx
  rw [← hgram] at hx ⊢
  rw [scoreVariance_eq_frame v hx]
  have hpoint (j : FrameIndex v) :
      (inner ℝ (frameCoefficients v j) (StoppedGaussianFeatures.stoppedRow σ target center (lo,x)))^2 ≤
        C * (ell*(hi-lo))⁻¹ * StoppedHeatSpanEnvelope.weight σ target center lo hi x := by
    rw [← StoppedScoreLeverage.realHistory_eq_inner σ target center (a j), hRx j]
    exact (hEx j).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hn j) hC.le)
      (StoppedHeatSpanEnvelope.weight_nonneg σ target center lo hi x))
  calc
    _ ≤ ∑ _j : FrameIndex v, C * (ell*(hi-lo))⁻¹ * StoppedHeatSpanEnvelope.weight σ target center lo hi x :=
      Finset.sum_le_sum (fun j _ => hpoint j)
    _ ≤ _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, div_eq_mul_inv]
      have hcard : (Fintype.card (FrameIndex v) : ℝ) ≤ (n:ℝ)+1 := by
        have hh : (Fintype.card (FrameIndex v) : ℝ) ≤ (n:ℝ) := by exact_mod_cast frame_card_le v
        linarith
      have hw0 := StoppedHeatSpanEnvelope.weight_nonneg σ target center lo hi x
      have hm := mul_le_mul_of_nonneg_right hcard
        (mul_nonneg (mul_nonneg hC.le (inv_nonneg.mpr hden.le)) hw0)
      convert! hm using 1 <;> ring

end SHE.IntervalScoreEnvelope
