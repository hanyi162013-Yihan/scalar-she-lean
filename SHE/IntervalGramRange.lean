module

public import SHE.OldIntervalRange

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.OldIntervalCovariance
open Set Filter MeasureTheory ProbabilityTheory AddCircle GaussianIncrement GaussianProfileMark
  StoppedGaussianFeatures StoppedFourier StoppedProfileMark ProfileVariance
open scoped Topology BigOperators Matrix.Norms.L2Operator
local instance intervalGramRange_periodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {n : ℕ}

theorem interval_row_energy_integrable (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) {lo hi : ℝ} (hlo : 0 ≤ lo) :
    Integrable (fun p => ‖stoppedRow σ target center p‖ ^ 2) (intervalMeasure lo hi) := by
  rw [intervalMeasure_eq_restrict hlo]
  exact (StoppedScoreLeverage.row_energy_integrable σ target center hages 0).restrict

theorem interval_weighted_energy_integrable (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) {lo hi M : ℝ} (hlo : 0 ≤ lo)
    (c : Domain → ℝ) (hc : Measurable c) (hb : ∀ p, |c p| ≤ M) :
    Integrable (fun p => |c p| * ‖stoppedRow σ target center p‖ ^ 2) (intervalMeasure lo hi) := by
  have he := interval_row_energy_integrable σ target center hages (hi := hi) hlo
  apply (he.const_mul M).mono'
    (hc.norm.mul ((stoppedRow_measurable σ target center).norm.pow_const 2)).aestronglyMeasurable
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_right (hb p) (sq_nonneg _)

/-- The exact interval Gram identity holds for arbitrary original stopping
times and targets. No artificial positive-stop or unit-horizon restriction
is needed. -/
theorem covariance_eq_interval_gram (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (c : Domain → ℝ) (hc : Measurable c)
    {M lo hi : ℝ} (hb : ∀ p, |c p| ≤ M) (hlo : 0 ≤ lo) :
    stoppedCovariance σ target center (intervalProfile c lo hi) 0 =
      profileCovariance (intervalMeasure lo hi) c (stoppedRow σ target center) := by
  have hInt := profileCovariance_integrable (intervalMeasure lo hi) c (stoppedRow σ target center)
    hc.aestronglyMeasurable (stoppedRow_measurable σ target center).aestronglyMeasurable
    (interval_weighted_energy_integrable σ target center hages hlo c hc hb)
  ext i j
  rw [profileCovariance_entries _ _ _ hInt]
  unfold StoppedGaussianFeatures.stoppedCovariance
  have he : (fun p => intervalProfile c lo hi p * stoppedRow σ target center p i * stoppedRow σ target center p j) =
      (timeSet lo hi).indicator (fun p => c p * stoppedRow σ target center p i * stoppedRow σ target center p j) := by
    funext p
    by_cases hp : p ∈ timeSet lo hi
    · simp only [intervalProfile, Set.indicator_of_mem hp]
    · simp only [intervalProfile, Set.indicator_of_notMem hp, zero_mul]
  rw [he, integral_indicator (show MeasurableSet (timeSet lo hi) from
    measurableSet_Ioc.prod MeasurableSet.univ), ← intervalMeasure_eq_restrict hlo]

theorem endpoint_row_mem_range_unrestricted (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) {lo hi ell M : ℝ} (hlo : 0 ≤ lo) (hgap : lo < hi)
    (hstop : ∀ i, σ i ≤ lo ∨ hi ≤ σ i)
    (c : Domain → ℝ) (hc : Measurable c) (hell : 0 < ell)
    (hb : ∀ p, ell ≤ c p ∧ c p ≤ M) :
    ∀ᵐ x : HeatCircle ∂haarAddCircle,
      stoppedRow σ target center (lo, x) ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ)
        (stoppedCovariance σ target center (intervalProfile c lo hi) 0)).range := by
  let row := stoppedRow σ target center
  let μ := intervalMeasure lo hi
  let S := (Matrix.toEuclideanCLM (𝕜 := ℝ)
    (stoppedCovariance σ target center (intervalProfile c lo hi) 0)).range
  have hrow : Measurable row := stoppedRow_measurable σ target center
  have henergy := interval_row_energy_integrable σ target center hages (hi := hi) hlo
  have hab : ∀ p, |c p| ≤ M := fun p => by
    rw [abs_of_nonneg (hell.le.trans (hb p).1)]
    exact (hb p).2
  have hci := interval_weighted_energy_integrable σ target center hages (hi := hi) hlo c hc hab
  have hrange := GaussianWordCovarianceIntegral.ae_frame_mem_profile_range μ row
    hrow.aestronglyMeasurable henergy c hc.aestronglyMeasurable hci hell
    (ae_of_all _ (fun p => (hb p).1))
  rw [← covariance_eq_interval_gram σ target center hages c hc hab hlo] at hrange
  have hset : MeasurableSet {p : Domain | row p ∈ S} := S.closed_of_finiteDimensional.measurableSet.preimage hrow
  have htime : ∀ᵐ x : HeatCircle ∂haarAddCircle, ∀ᵐ r ∂volume.restrict (Ioc lo hi), row (r, x) ∈ S :=
    (Measure.ae_ae_comm hset).mp (Measure.ae_ae_of_ae_prod hrange)
  filter_upwards [htime] with x hx
  exact ClosedIntervalRange.endpoint_mem S (show lo < (lo + hi) / 2 by linarith)
    (show (lo + hi) / 2 ≤ hi by linarith) (fun r => row (r, x))
    (continuousOn_row_time σ target center hages (show (lo + hi) / 2 < hi by linarith) hstop x) hx

end SHE.OldIntervalCovariance
