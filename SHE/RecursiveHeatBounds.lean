module

public import SHE.HeatCutoffHistories

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u

namespace SHE.RecursiveHeatBounds
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open CutoffInsertionCore GaussianItoTest SmoothCylinders SmoothWords UniformSmooth
open Classical
open scoped NNReal
variable {P : Type u} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n) (δ : ℝ) (hδ : 0 < δ)

def level (ε : ℝ≥0) (k : ℕ) : CutoffWordLevel.Level R (History P k) (n+k) :=
  HeatCutoffHistories.iterate L δ ε hδ ε.2 k

def test (k : ℕ) (p : ℝ≥0 × History P k) : WordRecursion.State (n+k) → ℝ :=
  (level L δ hδ p.1 k).test p.2

/-- For every fixed depth and time cutoff, every derivative bound is
uniform in the spatial heat age ε, including ε=0. This is the actual
recursively ε-dependent test, rather than a fixed test. -/
theorem test_uniform (k : ℕ) : UniformBoundedSmooth (test L δ hδ k) := by
  induction k with
  | zero => exact uniform_reindex L.test_uniform Prod.snd
  | succ k ih =>
    let Q := ℝ≥0 × History P (k+1)
    let old : Q → ℝ≥0 × History P k := fun p => (p.1,p.2.1)
    let hp : Q → History P k × (ℝ × HeatCircle) := fun p => p.2
    have hG := (uniform_reindex ih old).average
      (fun p : Q => ProbabilityTheory.multivariateGaussian (0 : WordRecursion.State (n+k))
        ((level L δ hδ p.1 k).nodeCovariance (hp p)).val) (fun _ => inferInstance)
    exact core_uniform R.totalVariance_smooth hG
      (fun p : Q => R.reference ((level L δ hδ p.1 k).nodeTime (hp p),(hp p).2.2))
      (fun p : Q => (level L δ hδ p.1 k).cutoffRow δ (hp p)) R.upper_nonneg
      (fun _ => R.reference_bound _) (mul_nonneg (Real.sqrt_nonneg _) (CovarianceMatrix.heatRowBound_pos hδ).le)
      (fun p => (level L δ hδ p.1 k).cutoffRow_bound hδ (hp p))

def averagedTest (k : ℕ) (p : ℝ≥0 × (History P k × (ℝ × HeatCircle))) : WordRecursion.State (n+k) → ℝ :=
  (level L δ hδ p.1 k).averagedTest p.2

theorem averagedTest_uniform (k : ℕ) : UniformBoundedSmooth (averagedTest L δ hδ k) := by
  let Q := ℝ≥0 × (History P k × (ℝ × HeatCircle))
  have hi := uniform_reindex (test_uniform L δ hδ k) (fun p : Q => (p.1,p.2.1))
  have hh := hi.average
    (fun p : Q => ProbabilityTheory.multivariateGaussian (0 : WordRecursion.State (n+k))
      ((level L δ hδ p.1 k).nodeCovariance p.2).val) (fun _ => inferInstance)
  exact hh

/-- The recursive node times are independent of ε: heat regularization
changes targets, and leaves every original stopping time unchanged. -/
theorem terminal_eq (ε η : ℝ≥0) (k : ℕ) (p : History P k) :
    (level L δ hδ ε k).terminal p=(level L δ hδ η k).terminal p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change ClippedCovariance.clip R.base ((level L δ hδ ε k).terminal p.1) p.2.1=
      ClippedCovariance.clip R.base ((level L δ hδ η k).terminal p.1) p.2.1
    rw [ih p.1]

theorem nodeTime_eq (ε η : ℝ≥0) (k : ℕ) (p : History P k × (ℝ × HeatCircle)) :
    (level L δ hδ ε k).nodeTime p=(level L δ hδ η k).nodeTime p := by
  change ClippedCovariance.clip R.base ((level L δ hδ ε k).terminal p.1) p.2.1=
    ClippedCovariance.clip R.base ((level L δ hδ η k).terminal p.1) p.2.1
  rw [terminal_eq L δ hδ ε η k p.1]

end SHE.RecursiveHeatBounds
