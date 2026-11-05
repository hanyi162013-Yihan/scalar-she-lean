module

public import SHE.OldIntervalCovariance
public import SHE.GaussianWordCovarianceIntegral

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.OldIntervalCovariance
open Set Filter MeasureTheory ProbabilityTheory AddCircle GaussianIncrement GaussianProfileMark
  StoppedGaussianFeatures StoppedFourier StoppedProfileMark ProfileVariance
open scoped Topology BigOperators Matrix.Norms.L2Operator
local instance oldIntervalRange_periodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {n : ℕ}

/-- On a genuine old interval every original stop is either already past
or still in the future. The literal stopped row is therefore continuous
from the interval's lower endpoint, with no alteration of its masks. -/
theorem continuousOn_row_time (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) {lo hi mid : ℝ} (hmh : mid < hi)
    (hstop : ∀ i, σ i ≤ lo ∨ hi ≤ σ i) (x : HeatCircle) :
    ContinuousOn (fun r => stoppedRow σ target center (r, x)) (Icc lo mid) := by
  have htoLp : Continuous (WithLp.toLp 2 : (Fin n → ℝ) → State n) :=
    PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)
  apply htoLp.comp_continuousOn
  apply continuousOn_pi.mpr
  intro i
  change ContinuousOn (fun r => if r < σ i then (heatPhysical (target i - r) (center i) x).re else 0) _
  rcases hstop i with hbefore | hafter
  · apply (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc lo mid)).congr
    intro r hr
    dsimp only
    rw [if_neg (by linarith [hr.1])]
  · have hc : ContinuousOn (fun r => (heatPhysical (target i - r) (center i) x).re) (Icc lo mid) := by
      intro r hr
      have ha : 0 < target i - r := by linarith [hr.2, hages i]
      exact (Complex.continuous_re.continuousAt.comp
        ((HeatAgeContinuity.continuousAt_heatPhysical_age ha (center i) x).comp
          ((continuous_const.sub continuous_id).continuousAt))).continuousWithinAt
    apply hc.congr
    intro r hr
    dsimp only
    rw [if_pos (by linarith [hr.2])]

/-- Actual old-interval covariance range applicability at the insertion
time. The conclusion holds for almost every original spatial point, as
required by physical word integration. It follows from the actual weighted
Gram, Fubini, right continuity, and closedness of the finite range. -/
theorem endpoint_row_mem_range_ae (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hσ : ∀ i, 0 < σ i) (hσ1 : ∀ i, σ i ≤ 1) (hages : ∀ i, σ i ≤ target i)
    {lo hi ell M : ℝ} (hlo : 0 ≤ lo) (hgap : lo < hi)
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
  have hM : 0 ≤ M := (hell.le.trans (hb (0, 0)).1).trans (hb (0, 0)).2
  have hrow : Measurable row := stoppedRow_measurable σ target center
  have henergy : Integrable (fun p => ‖row p‖ ^ 2) μ := by
    rw [show μ = (historyMeasure 0).restrict (timeSet lo hi) from intervalMeasure_eq_restrict hlo]
    exact (StoppedScoreLeverage.row_energy_integrable σ target center hages 0).restrict
  have hci : Integrable (fun p => |c p| * ‖row p‖ ^ 2) μ := by
    apply (henergy.const_mul M).mono'
      (by convert! (hc.norm.mul (hrow.norm.pow_const 2)).aestronglyMeasurable using 1)
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _)),
      abs_of_nonneg (hell.le.trans (hb p).1)]
    exact mul_le_mul_of_nonneg_right (hb p).2 (sq_nonneg _)
  have hrange := GaussianWordCovarianceIntegral.ae_frame_mem_profile_range μ row
    hrow.aestronglyMeasurable henergy c hc.aestronglyMeasurable hci hell
    (ae_of_all _ (fun p => (hb p).1))
  have heq := covariance_eq_profileCovariance σ target center hσ hσ1 hages c hc (hi := hi) hM
    (fun p => by rw [abs_of_nonneg (hell.le.trans (hb p).1)]; exact (hb p).2) hlo
  rw [← heq] at hrange
  have hset : MeasurableSet {p : Domain | row p ∈ S} := S.closed_of_finiteDimensional.measurableSet.preimage hrow
  have htime : ∀ᵐ x : HeatCircle ∂haarAddCircle, ∀ᵐ r ∂volume.restrict (Ioc lo hi), row (r, x) ∈ S :=
    (Measure.ae_ae_comm hset).mp (Measure.ae_ae_of_ae_prod hrange)
  filter_upwards [htime] with x hx
  apply ClosedIntervalRange.endpoint_mem S (show lo < (lo + hi) / 2 by linarith)
    (show (lo + hi) / 2 ≤ hi by linarith) (fun r => row (r, x))
    (continuousOn_row_time σ target center hages (show (lo + hi) / 2 < hi by linarith) hstop x) hx

end SHE.OldIntervalCovariance
