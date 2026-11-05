module

public import SHE.IntervalHistoryEnergy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.IntervalScoreMass
open Set Filter MeasureTheory ProbabilityTheory AddCircle GaussianIncrement StoppedGaussianFeatures
  StoppedFourier OldIntervalCovariance GaussianGramScore MeasurableGaussianScores GaussianProfileMark
open scoped BigOperators InnerProductSpace
local instance intervalScoreMass_periodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {n : ℕ}

theorem intervalBounds (c : Domain → ℝ) {M : ℝ} (hcb : ∀ p, 0 ≤ c p ∧ c p ≤ M)
    (lo hi : ℝ) (p : Domain) :
    0 ≤ intervalProfile c lo hi p ∧ intervalProfile c lo hi p ≤ M := by
  by_cases hp : p ∈ timeSet lo hi
  · simpa only [intervalProfile, Set.indicator_of_mem hp] using hcb p
  · simp only [intervalProfile, Set.indicator_of_notMem hp, le_refl, true_and]
    exact (hcb p).1.trans (hcb p).2

def feature (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (c : Domain → ℝ) (hc : Measurable c)
    (M : ℝ) (hcb : ∀ p, 0 ≤ c p ∧ c p ≤ M) (lo hi : ℝ) :
    Fin n → Lp ℝ 2 (StoppedGaussianFeatures.historyMeasure 0) :=
  weightedFeature σ target center (intervalProfile c lo hi) (measurable_intervalProfile hc lo hi)
    M (intervalBounds c hcb lo hi) hages 0

theorem feature_gram (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (c : Domain → ℝ) (hc : Measurable c)
    (M : ℝ) (hcb : ∀ p, 0 ≤ c p ∧ c p ≤ M) (lo hi : ℝ) :
    Matrix.gram ℝ (feature σ target center hages c hc M hcb lo hi) =
      StoppedGaussianFeatures.stoppedCovariance σ target center (intervalProfile c lo hi) 0 :=
  weightedFeature_gram σ target center (intervalProfile c lo hi) (measurable_intervalProfile hc lo hi)
    M (intervalBounds c hcb lo hi) hages 0

theorem synthesis_norm_sq (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (c : Domain → ℝ) (hc : Measurable c)
    (M : ℝ) (hcb : ∀ p, 0 ≤ c p ∧ c p ≤ M) {lo hi : ℝ} (hlo : 0 ≤ lo) (z : State n) :
    ‖featureSynthesis (feature σ target center hages c hc M hcb lo hi) z‖ ^ 2 =
      ∫ p, c p * realHistory σ target center z p ^ 2 ∂intervalMeasure lo hi := by
  rw [feature, weightedSynthesis_norm_sq]
  have he : (fun p => intervalProfile c lo hi p * realHistory σ target center z p ^ 2) =
      (timeSet lo hi).indicator (fun p => c p * realHistory σ target center z p ^ 2) := by
    funext p
    by_cases hp : p ∈ timeSet lo hi
    · simp only [intervalProfile, Set.indicator_of_mem hp]
    · simp only [intervalProfile, Set.indicator_of_notMem hp, zero_mul]
  rw [he, integral_indicator (show MeasurableSet (timeSet lo hi) from
    measurableSet_Ioc.prod MeasurableSet.univ), ← intervalMeasure_eq_restrict hlo]

/-- Actual interval covariance dominates the spatial insertion Gram with
the exact factor ell times the interval length. -/
theorem endpoint_domination (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (c : Domain → ℝ) (hc : Measurable c)
    {lo hi ell M : ℝ} (hlo : 0 ≤ lo) (hgap : lo < hi)
    (hstop : ∀ i, σ i ≤ lo ∨ hi ≤ σ i) (hell : 0 < ell)
    (hb : ∀ p, ell ≤ c p ∧ c p ≤ M) (z : State n) :
    ell * (hi-lo) * (∫ x, realHistory σ target center z (lo,x) ^ 2 ∂haarAddCircle) ≤
      ‖featureSynthesis (feature σ target center hages c hc M
        (fun p => ⟨hell.le.trans (hb p).1, (hb p).2⟩) lo hi) z‖ ^ 2 := by
  rw [synthesis_norm_sq _ _ _ _ _ _ _ _ hlo]
  exact IntervalHistoryEnergy.weighted_endpoint_energy_le σ target center hages z hlo hgap hstop c hc hell hb

/-- The actual canonical old insertion score has spatial mass at most
the number of observations divided by ell times its original interval
length. Singular and colliding observation configurations are included. -/
theorem score_mass_bound (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (c : Domain → ℝ) (hc : Measurable c)
    {lo hi ell M : ℝ} (hlo : 0 ≤ lo) (hgap : lo < hi)
    (hstop : ∀ i, σ i ≤ lo ∨ hi ≤ σ i) (hell : 0 < ell)
    (hb : ∀ p, ell ≤ c p ∧ c p ≤ M) :
    Integrable (fun x => scoreVariance
      (StoppedGaussianFeatures.stoppedCovariance σ target center (intervalProfile c lo hi) 0)
      (StoppedGaussianFeatures.stoppedRow σ target center (lo,x))) haarAddCircle ∧
      (∫ x, scoreVariance (StoppedGaussianFeatures.stoppedCovariance σ target center (intervalProfile c lo hi) 0)
        (StoppedGaussianFeatures.stoppedRow σ target center (lo,x)) ∂haarAddCircle) ≤
          (n : ℝ) / (ell * (hi-lo)) := by
  let v := feature σ target center hages c hc M (fun p => ⟨hell.le.trans (hb p).1, (hb p).2⟩) lo hi
  let a := frameCoefficients v
  have hden : 0 < ell * (hi-lo) := mul_pos hell (sub_pos.mpr hgap)
  have hgram : Matrix.gram ℝ v =
      StoppedGaussianFeatures.stoppedCovariance σ target center (intervalProfile c lo hi) 0 :=
    feature_gram σ target center hages c hc M (fun p => ⟨hell.le.trans (hb p).1, (hb p).2⟩) lo hi
  have hrow := endpoint_row_mem_range_unrestricted σ target center hages hlo hgap hstop c hc hell hb
  have heq : (fun x => scoreVariance (Matrix.gram ℝ v)
      (StoppedGaussianFeatures.stoppedRow σ target center (lo,x))) =ᵐ[haarAddCircle]
      fun x => ∑ j : FrameIndex v, realHistory σ target center (a j) (lo,x) ^ 2 := by
    filter_upwards [hrow] with x hx
    have hx' : StoppedGaussianFeatures.stoppedRow σ target center (lo,x) ∈
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.gram ℝ v)).range := by rwa [hgram]
    rw [scoreVariance_eq_frame v hx']
    exact Finset.sum_congr rfl (fun j _ => by rw [StoppedScoreLeverage.realHistory_eq_inner])
  have hInt (j : FrameIndex v) : Integrable (fun x => realHistory σ target center (a j) (lo,x) ^ 2) haarAddCircle :=
    realHistory_square_integrable σ target center hages (a j) lo
  have hiSum := integrable_finsetSum Finset.univ (fun j _ => hInt j)
  have hiScore := hiSum.congr heq.symm
  have hmass (j : FrameIndex v) :
      (∫ x, realHistory σ target center (a j) (lo,x) ^ 2 ∂haarAddCircle) ≤ (ell*(hi-lo))⁻¹ := by
    have hh := endpoint_domination σ target center hages c hc hlo hgap hstop hell hb (a j)
    rw [(frameCoefficients_orthonormal v).norm_eq_one j, one_pow] at hh
    rw [inv_eq_one_div, le_div_iff₀ hden]
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hh
  refine ⟨by simpa only [hgram] using hiScore, ?_⟩
  rw [← hgram]
  calc
    _ = ∑ j : FrameIndex v, ∫ x, realHistory σ target center (a j) (lo,x) ^ 2 ∂haarAddCircle := by
      rw [integral_congr_ae heq, integral_finsetSum Finset.univ (fun j _ => hInt j)]
    _ ≤ ∑ _j : FrameIndex v, (ell*(hi-lo))⁻¹ := Finset.sum_le_sum (fun j _ => hmass j)
    _ ≤ (n : ℝ) / (ell*(hi-lo)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast frame_card_le v) (inv_nonneg.mpr hden.le)

end SHE.IntervalScoreMass
