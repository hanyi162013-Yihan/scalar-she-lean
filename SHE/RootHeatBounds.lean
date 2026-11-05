module

public import SHE.RecursiveHeatBounds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.RootHeatBounds
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open CutoffInsertionCore GaussianItoTest SmoothCylinders SmoothWords UniformSmooth
open Classical
open scoped NNReal
variable {P : Type*} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}

/-- Heat regularize every original observation, preserving its ORIGINAL
stop. The inserted observations will receive the same positive heat age.
This gives a real positive-gap approximation even when the root stop and
target coincide. -/
def shift (L : Level R P n) (ε : ℝ≥0) : Level R P n where
  observations := {
    observations := fun p i => {(L.observations.observations p i) with
      target := (L.observations.observations p i).target+(ε:ℝ)}
    stop_measurable := L.observations.stop_measurable
    target_measurable := fun i => (L.observations.target_measurable i).add_const _
    center_measurable := L.observations.center_measurable }
  terminal := L.terminal
  terminal_measurable := L.terminal_measurable
  terminal_base := L.terminal_base
  terminal_horizon := L.terminal_horizon
  targets_after := fun p i => (L.targets_after p i).trans (le_add_of_nonneg_right ε.2)
  stops_after := L.stops_after
  test := L.test
  test_uniform := L.test_uniform
  test_measurable := L.test_measurable

theorem shift_gap (L : Level R P n) (ε : ℝ≥0) : HeatCutoffHistories.Gap (shift L ε) (ε:ℝ) := by
  intro p i
  change (ε:ℝ)≤(L.observations.observations p i).target+(ε:ℝ)-L.terminal p
  linarith [L.targets_after p i]

variable (L : Level R P n) (δ : ℝ) (hδ : 0<δ)

def level (ε : ℝ≥0) (k : ℕ) : Level R (History P k) (n+k) :=
  RecursiveHeatBounds.level (shift L ε) δ hδ ε k

theorem level_gap (ε : ℝ≥0) (k : ℕ) : HeatCutoffHistories.Gap (level L δ hδ ε k) (ε:ℝ) :=
  HeatCutoffHistories.iterate_gap (shift L ε) hδ ε.2 (shift_gap L ε) k

def test (k : ℕ) (p : ℝ≥0×History P k) : WordRecursion.State (n+k)→ℝ :=
  (level L δ hδ p.1 k).test p.2

/-- Every finite state derivative remains uniform in the heat age of
BOTH the original root and all recursively inserted observations. -/
theorem test_uniform (k : ℕ) : UniformBoundedSmooth (test L δ hδ k) := by
  induction k with
  | zero => exact uniform_reindex L.test_uniform Prod.snd
  | succ k ih =>
    let Q := ℝ≥0×History P (k+1)
    let old : Q→ℝ≥0×History P k := fun p => (p.1,p.2.1)
    let hp : Q→History P k×(ℝ×HeatCircle) := fun p => p.2
    have hG := (uniform_reindex ih old).average
      (fun p : Q => ProbabilityTheory.multivariateGaussian (0:WordRecursion.State (n+k))
        ((level L δ hδ p.1 k).nodeCovariance (hp p)).val) (fun _ => inferInstance)
    exact core_uniform R.totalVariance_smooth hG
      (fun p : Q => R.reference ((level L δ hδ p.1 k).nodeTime (hp p),(hp p).2.2))
      (fun p : Q => (level L δ hδ p.1 k).cutoffRow δ (hp p)) R.upper_nonneg
      (fun _ => R.reference_bound _)
      (mul_nonneg (Real.sqrt_nonneg _) (CovarianceMatrix.heatRowBound_pos hδ).le)
      (fun p => (level L δ hδ p.1 k).cutoffRow_bound hδ (hp p))

def averagedTest (k : ℕ) (p : ℝ≥0×(History P k×(ℝ×HeatCircle))) : WordRecursion.State (n+k)→ℝ :=
  (level L δ hδ p.1 k).averagedTest p.2

theorem averagedTest_uniform (k : ℕ) : UniformBoundedSmooth (averagedTest L δ hδ k) := by
  let Q := ℝ≥0×(History P k×(ℝ×HeatCircle))
  have hi := uniform_reindex (test_uniform L δ hδ k) (fun p : Q => (p.1,p.2.1))
  exact hi.average
    (fun p : Q => ProbabilityTheory.multivariateGaussian (0:WordRecursion.State (n+k))
      ((level L δ hδ p.1 k).nodeCovariance p.2).val) (fun _ => inferInstance)

theorem terminal_eq (ε η : ℝ≥0) (k : ℕ) (p : History P k) :
    (level L δ hδ ε k).terminal p=(level L δ hδ η k).terminal p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change ClippedCovariance.clip R.base ((level L δ hδ ε k).terminal p.1) p.2.1=
      ClippedCovariance.clip R.base ((level L δ hδ η k).terminal p.1) p.2.1
    rw [ih p.1]

theorem nodeTime_eq (ε η : ℝ≥0) (k : ℕ) (p : History P k×(ℝ×HeatCircle)) :
    (level L δ hδ ε k).nodeTime p=(level L δ hδ η k).nodeTime p := by
  change ClippedCovariance.clip R.base ((level L δ hδ ε k).terminal p.1) p.2.1=
    ClippedCovariance.clip R.base ((level L δ hδ η k).terminal p.1) p.2.1
  rw [terminal_eq L δ hδ ε η k p.1]

theorem level_zero (k : ℕ) : level L δ hδ 0 k=RecursiveHeatBounds.level L δ hδ 0 k := by
  have hs : shift L 0=L := by
    cases L
    simp only [shift,NNReal.coe_zero,add_zero]
  rw [level,hs]

end SHE.RootHeatBounds
