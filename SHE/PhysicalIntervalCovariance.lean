module

public import SHE.OldIntervalRange
public import SHE.CovarianceEndpoint

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.PhysicalIntervalCovariance
open Set Filter MeasureTheory ProbabilityTheory AddCircle GaussianIncrement StoppedGaussianFeatures
  StoppedFourier OldIntervalCovariance WordRecursion
open scoped BigOperators Matrix.Norms.L2Operator
local instance physicalIntervalCovariance_periodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {n : ℕ}

/-- The individually stopped covariance on an old interval is exactly
the literal recursive-word covariance when the interval precedes all stops.
The potentially colliding upper endpoint is removed only on a null set. -/
theorem interval_eq_covariance (Z : Fin n → Observation) (c : Domain → ℝ)
    (hc : Measurable c) {M lo hi : ℝ} (hb : ∀ p, |c p| ≤ M)
    (hages : ∀ i, (Z i).stop ≤ (Z i).target) (hstop : ∀ i, hi ≤ (Z i).stop)
    (hlo : 0 ≤ lo) (hgap : lo ≤ hi) :
    stoppedCovariance (fun i => (Z i).stop) (fun i => (Z i).target) (fun i => (Z i).center)
      (intervalProfile c lo hi) 0 = covariance c Z lo hi := by
  let row := stoppedRow (fun i => (Z i).stop) (fun i => (Z i).target) (fun i => (Z i).center)
  ext i j
  have hi0 := StoppedCovarianceSplit.covariance_entry_integrable
    (fun i => (Z i).stop) (fun i => (Z i).target) (fun i => (Z i).center) hages 0 hc hb i j
  have hfi : Integrable (fun p => c p * row p i * row p j) (intervalMeasure lo hi) := by
    rw [intervalMeasure_eq_restrict hlo]
    exact hi0.restrict
  have he : (fun p : Domain => intervalProfile c lo hi p * row p i * row p j) =
      (timeSet lo hi).indicator (fun p => c p * row p i * row p j) := by
    funext p
    by_cases hp : p ∈ timeSet lo hi
    · simp only [intervalProfile, Set.indicator_of_mem hp]
    · simp only [intervalProfile, Set.indicator_of_notMem hp, zero_mul]
  change (∫ p, intervalProfile c lo hi p * row p i * row p j ∂historyMeasure 0) = _
  rw [he, integral_indicator (show MeasurableSet (timeSet lo hi) from
    measurableSet_Ioc.prod MeasurableSet.univ),
    ← intervalMeasure_eq_restrict hlo, intervalMeasure, integral_prod _ hfi]
  change _ = ∫ t in lo..hi, covarianceDensity c Z t i j
  rw [intervalIntegral.integral_of_le hgap]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae (volume.ae_ne hi)] with t ht hne
  have hthi : t < hi := lt_of_le_of_ne ht.2 hne
  apply integral_congr_ae
  apply ae_of_all
  intro x
  dsimp only [row, stoppedRow, heatRow, covarianceDensity]
  rw [ite_eq_left (hthi.trans_le (hstop i)), ite_eq_left (hthi.trans_le (hstop j))]

theorem covariance_const_mul (Z : Fin n → Observation) (c : Domain → ℝ) (a lo hi : ℝ) :
    covariance (fun p => a * c p) Z lo hi = a • covariance c Z lo hi := by
  ext i j
  simp only [WordRecursion.covariance, covarianceDensity, Matrix.smul_apply, smul_eq_mul, mul_assoc,
    integral_const_mul, intervalIntegral.integral_const_mul]

theorem covariance_add (Z : Fin n → Observation) (c d : Domain → ℝ)
    (hc : Measurable c) (hd : Measurable d) {M N lo hi : ℝ}
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hgap : lo ≤ hi)
    (hafter : ∀ i, hi ≤ (Z i).target) (hb : ∀ p, |c p| ≤ M) (hdb : ∀ p, |d p| ≤ N) :
    WordRecursion.covariance (fun p => c p + d p) Z lo hi =
      WordRecursion.covariance c Z lo hi + WordRecursion.covariance d Z lo hi := by
  ext i j
  have hci := CovarianceEndpoint.covariance_entry_intervalIntegrable_endpoint c hc Z hM hgap hafter
    (fun t _ x => hb (t,x)) i j
  have hdi := CovarianceEndpoint.covariance_entry_intervalIntegrable_endpoint d hd Z hN hgap hafter
    (fun t _ x => hdb (t,x)) i j
  have hspace (t : ℝ) (ht : lo < t ∧ t < hi) :
      covarianceDensity (fun p => c p + d p) Z t i j = covarianceDensity c Z t i j + covarianceDensity d Z t i j := by
    have htarget : ∀ l, 0 < (Z l).target - t := fun l => sub_pos.mpr (ht.2.trans_le (hafter l))
    have h1 := CovarianceMatrix.covariance_spatial_integrable c hc Z (sub_pos.mpr ht.2) hM
      (fun l => by linarith [hafter l]) (le_rfl : t ≤ t) (fun x => hb (t,x)) i j
    have h2 := CovarianceMatrix.covariance_spatial_integrable d hd Z (sub_pos.mpr ht.2) hN
      (fun l => by linarith [hafter l]) (le_rfl : t ≤ t) (fun x => hdb (t,x)) i j
    simp only [covarianceDensity, add_mul]
    exact integral_add h1 h2
  change (∫ t in lo..hi, covarianceDensity (fun p => c p + d p) Z t i j) = _
  rw [show (WordRecursion.covariance c Z lo hi + WordRecursion.covariance d Z lo hi) i j =
    (∫ t in lo..hi, covarianceDensity c Z t i j) + (∫ t in lo..hi, covarianceDensity d Z t i j) from rfl,
    ← intervalIntegral.integral_add hci hdi]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le hgap]
  filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae (volume.ae_ne hi)] with t ht hn
  exact hspace t ⟨ht.1, lt_of_le_of_ne ht.2 hn⟩

/-- Endpoint range applicability in the exact recursive-word covariance. -/
theorem heatRow_mem_range_ae (Z : Fin n → Observation) (c : Domain → ℝ)
    (hc : Measurable c) {ell M lo hi : ℝ} (hell : 0 < ell)
    (hb : ∀ p, ell ≤ c p ∧ c p ≤ M)
    (hages : ∀ i, (Z i).stop ≤ (Z i).target) (hstop : ∀ i, hi ≤ (Z i).stop)
    (hstop1 : ∀ i, (Z i).stop ≤ 1) (hlo : 0 ≤ lo) (hgap : lo < hi) :
    ∀ᵐ x : HeatCircle ∂haarAddCircle,
      heatRow Z lo x ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (covariance c Z lo hi)).range := by
  have hh := endpoint_row_mem_range_ae (fun i => (Z i).stop) (fun i => (Z i).target)
    (fun i => (Z i).center) (fun i => lt_of_lt_of_le (hlo.trans_lt hgap) (hstop i)) hstop1 hages hlo hgap
    (fun i => Or.inr (hstop i)) c hc hell hb
  rw [interval_eq_covariance Z c hc (fun p => by rw [abs_of_nonneg (hell.le.trans (hb p).1)]; exact (hb p).2)
    hages hstop hlo hgap.le] at hh
  filter_upwards [hh] with x hx
  convert hx using 1
  ext i
  simp only [heatRow, stoppedRow, ite_eq_left (lt_of_lt_of_le hgap (hstop i))]

end SHE.PhysicalIntervalCovariance
