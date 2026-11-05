module

public import SHE.GaussianAssignmentSupport
public import SHE.StoppedScoreLeverage
public import SHE.HeatAgeContinuity
public import SHE.ClosedIntervalRange
public import SHE.StoppedCovarianceSplit

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.OldIntervalCovariance
open Set Filter MeasureTheory ProbabilityTheory AddCircle GaussianIncrement GaussianProfileMark
  StoppedGaussianFeatures StoppedFourier StoppedProfileMark ProfileVariance
open scoped Topology BigOperators Matrix.Norms.L2Operator
local instance oldIntervalCovariance_periodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {n : ℕ}

def timeSet (lo hi : ℝ) : Set Domain := Ioc lo hi ×ˢ univ

def intervalProfile (c : Domain → ℝ) (lo hi : ℝ) : Domain → ℝ :=
  (timeSet lo hi).indicator c

def intervalMeasure (lo hi : ℝ) : Measure Domain :=
  (volume.restrict (Ioc lo hi)).prod (haarAddCircle (T := 2 * Real.pi))

theorem measurable_intervalProfile {c : Domain → ℝ} (hc : Measurable c) (lo hi : ℝ) :
    Measurable (intervalProfile c lo hi) := hc.indicator (measurableSet_Ioc.prod MeasurableSet.univ)

theorem intervalMeasure_eq_restrict {lo hi : ℝ} (hlo : 0 ≤ lo) :
    intervalMeasure lo hi = (historyMeasure 0).restrict (timeSet lo hi) := by
  unfold intervalMeasure historyMeasure timeSet
  rw [← Measure.restrict_prod_eq_prod_univ, Measure.restrict_restrict measurableSet_Ioc]
  congr 2
  exact (inter_eq_left.mpr (show Ioc lo hi ⊆ Ici 0 from fun r hr => hlo.trans hr.1.le)).symm

theorem profileCovariance_interval_eq {lo hi : ℝ} (hlo : 0 ≤ lo)
    (c : Domain → ℝ) (row : Domain → State n) :
    profileCovariance (historyMeasure 0) (intervalProfile c lo hi) row =
      profileCovariance (intervalMeasure lo hi) c row := by
  unfold profileCovariance
  have he : (fun p => intervalProfile c lo hi p • rankMatrix (row p)) =
      (timeSet lo hi).indicator (fun p => c p • rankMatrix (row p)) := by
    funext p
    unfold intervalProfile
    by_cases hp : p ∈ timeSet lo hi
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem hp, zero_smul, Set.indicator_of_notMem hp]
  have hI : MeasurableSet (timeSet lo hi) := measurableSet_Ioc.prod MeasurableSet.univ
  rw [he, integral_indicator hI, ← intervalMeasure_eq_restrict hlo]

theorem covariance_eq_profileCovariance (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hσ : ∀ i, 0 < σ i) (hσ1 : ∀ i, σ i ≤ 1) (hages : ∀ i, σ i ≤ target i)
    (c : Domain → ℝ) (hc : Measurable c) {M lo hi : ℝ} (hM : 0 ≤ M)
    (hb : ∀ p, |c p| ≤ M) (hlo : 0 ≤ lo) :
    stoppedCovariance σ target center (intervalProfile c lo hi) 0 =
      profileCovariance (intervalMeasure lo hi) c (stoppedRow σ target center) := by
  rw [← profileCovariance_eq_stopped σ target center hσ hσ1 hages (by norm_num : 0 ≤ (0 : ℝ))
    (measurable_intervalProfile hc lo hi) (fun p => by
      by_cases hp : p ∈ timeSet lo hi
      · simpa only [intervalProfile, Set.indicator_of_mem hp] using hb p
      · simp only [intervalProfile, Set.indicator_of_notMem hp, abs_zero, hM])]
  exact profileCovariance_interval_eq hlo c _

theorem covariance_posSemidef (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (c : Domain → ℝ) (hc : Measurable c)
    {M : ℝ} (hb : ∀ p, 0 ≤ c p ∧ c p ≤ M) (lo hi : ℝ) :
    (stoppedCovariance σ target center (intervalProfile c lo hi) 0).PosSemidef := by
  apply StoppedCovarianceSplit.covariance_posSemidef σ target center hages 0
    (measurable_intervalProfile hc lo hi)
  intro p
  by_cases hp : p ∈ timeSet lo hi
  · simpa only [intervalProfile, Set.indicator_of_mem hp] using hb p
  · simp only [intervalProfile, Set.indicator_of_notMem hp, le_refl, true_and]
    exact (hb p).1.trans (hb p).2

/-- Later physical leaves do not see any old interval lying after their
stopping time: their covariance row and column vanish exactly. -/
theorem covariance_inactive_row (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (c : Domain → ℝ) (lo hi : ℝ) (i j : Fin n) (hiStop : σ i ≤ lo) :
    stoppedCovariance σ target center (intervalProfile c lo hi) 0 i j = 0 := by
  unfold StoppedGaussianFeatures.stoppedCovariance
  apply integral_eq_zero_of_ae
  apply ae_of_all
  intro p
  by_cases hp : p ∈ timeSet lo hi
  · have hni : ¬p.1 < σ i := by have hpl := hp.1.1; linarith
    simp only [stoppedRow, hni, ite_false, mul_zero, zero_mul, Pi.zero_apply]
  · simp only [intervalProfile, Set.indicator_of_notMem hp, zero_mul, Pi.zero_apply]

theorem covariance_inactive_column (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (c : Domain → ℝ) (lo hi : ℝ) (i j : Fin n) (hiStop : σ j ≤ lo) :
    stoppedCovariance σ target center (intervalProfile c lo hi) 0 i j = 0 := by
  unfold StoppedGaussianFeatures.stoppedCovariance
  apply integral_eq_zero_of_ae
  apply ae_of_all
  intro p
  by_cases hp : p ∈ timeSet lo hi
  · have hnj : ¬p.1 < σ j := by have hpl := hp.1.1; linarith
    simp only [stoppedRow, hnj, ite_false, mul_zero, Pi.zero_apply]
  · simp only [intervalProfile, Set.indicator_of_notMem hp, zero_mul, Pi.zero_apply]

end SHE.OldIntervalCovariance
