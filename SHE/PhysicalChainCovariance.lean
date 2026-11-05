module

public import SHE.PhysicalScoreChain
public import SHE.GaussianScoreChainData

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.PhysicalScoreChain
open Set Filter MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord
  OldIntervalCovariance StoppedGaussianFeatures FixedOldScoreSupport
open scoped BigOperators Matrix.Norms.L2Operator
local instance physicalChainCovariance_periodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n N : ℕ}
variable (L : CutoffWordLevel.Level R P n)

def rootParameter : (k : ℕ) → History P k → P
  | 0 => fun p => p
  | k+1 => fun p => rootParameter k p.1

def initialTerminal (k : ℕ) (p : History P k) : ℝ := L.terminal (rootParameter k p)

theorem terminal_le_initial (k : ℕ) (p : History P k) :
    (carrier L k).terminal p ≤ initialTerminal L k p := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact ((carrier L k).nodeTime_mem p).2.trans (ih p.1)

theorem intervalProfile_add_adjacent (c : Domain → ℝ) {lo mid hi : ℝ}
    (hlm : lo ≤ mid) (hmh : mid ≤ hi) :
    (fun p => intervalProfile c lo mid p + intervalProfile c mid hi p) = intervalProfile c lo hi := by
  funext p
  by_cases h1 : p.1 ∈ Ioc lo mid
  · have h2 : p.1 ∉ Ioc mid hi := fun h => not_lt_of_ge h1.2 h.1
    have h3 : p.1 ∈ Ioc lo hi := ⟨h1.1, h1.2.trans hmh⟩
    simp only [intervalProfile, timeSet, mem_prod, mem_univ, and_true,
      Set.indicator, h1, h2, h3, ite_true, ite_false, add_zero]
  · by_cases h2 : p.1 ∈ Ioc mid hi
    · have h3 : p.1 ∈ Ioc lo hi := ⟨hlm.trans_lt h2.1, h2.2⟩
      simp only [intervalProfile, timeSet, mem_prod, mem_univ, and_true,
        Set.indicator, h1, h2, h3, ite_true, ite_false, zero_add]
    · have h3 : p.1 ∉ Ioc lo hi := by
        intro h
        by_cases ht : p.1 ≤ mid
        · exact h1 ⟨h.1, ht⟩
        · exact h2 ⟨lt_of_not_ge ht, h.2⟩
      simp only [intervalProfile, timeSet, mem_prod, mem_univ, and_true,
        Set.indicator, h1, h2, h3, ite_false, add_zero]

theorem profile_bound (c : Domain → ℝ) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ p, |c p| ≤ M)
    (lo hi : ℝ) (p : Domain) : |intervalProfile c lo hi p| ≤ M := by
  by_cases hp : p ∈ timeSet lo hi
  · simpa only [intervalProfile, Set.indicator_of_mem hp] using hb p
  · simpa only [intervalProfile, Set.indicator_of_notMem hp, abs_zero] using hM

theorem interval_add_profiles (Z : Fin N → Observation) (hZ : ∀ i, (Z i).stop ≤ (Z i).target)
    (c d : Domain → ℝ) (hc : Measurable c) (hd : Measurable d)
    {M J : ℝ} (hM : 0 ≤ M) (hJ : 0 ≤ J) (hb : ∀ p, |c p| ≤ M) (hdb : ∀ p, |d p| ≤ J)
    (lo hi : ℝ) :
    intervalCovariance Z (fun p => c p + d p) lo hi = intervalCovariance Z c lo hi + intervalCovariance Z d lo hi := by
  have he : intervalProfile (fun p => c p + d p) lo hi =
      fun p => intervalProfile c lo hi p + intervalProfile d lo hi p := by
    funext p
    by_cases hp : p ∈ timeSet lo hi <;>
      simp only [intervalProfile, Set.indicator, hp, ite_true, ite_false, add_zero]
  unfold intervalCovariance
  rw [he]
  exact StoppedCovarianceSplit.covariance_add _ _ _ hZ 0 (measurable_intervalProfile hc lo hi)
    (measurable_intervalProfile hd lo hi) (profile_bound c hM hb lo hi) (profile_bound d hJ hdb lo hi)

theorem interval_add_adjacent (Z : Fin N → Observation) (hZ : ∀ i, (Z i).stop ≤ (Z i).target)
    (c : Domain → ℝ) (hc : Measurable c) {M lo mid hi : ℝ}
    (hM : 0 ≤ M) (hb : ∀ p, |c p| ≤ M) (hlm : lo ≤ mid) (hmh : mid ≤ hi) :
    intervalCovariance Z c lo mid + intervalCovariance Z c mid hi = intervalCovariance Z c lo hi := by
  unfold intervalCovariance
  rw [← StoppedCovarianceSplit.covariance_add _ _ _ hZ 0 (measurable_intervalProfile hc lo mid)
    (measurable_intervalProfile hc mid hi) (profile_bound c hM hb lo mid) (profile_bound c hM hb mid hi),
    intervalProfile_add_adjacent c hlm hmh]

@[simp] theorem interval_same (Z : Fin N → Observation) (c : Domain → ℝ) (t : ℝ) :
    intervalCovariance Z c t t = 0 := by
  ext i j
  simp only [intervalCovariance, StoppedGaussianFeatures.stoppedCovariance, intervalProfile, timeSet,
    Ioc_self, empty_prod, Set.indicator_empty, Pi.zero_apply, zero_mul, integral_zero, Matrix.zero_apply]

/-- The old matrices are exactly one fixed old profile on the union of
the actual adjacent history intervals, independent of the interpolation. -/
theorem Physical.sum_old (Z : Fin N → Observation) (hZ : ∀ i, (Z i).stop ≤ (Z i).target)
    (c : Domain → ℝ) (hc : Measurable c) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ p, |c p| ≤ M)
    {k : ℕ} {p : History P k} {g : Fin (n+k) → Fin N} (chain : Chain L k p g)
    (hp : Physical L Z c chain) :
    (∑ j, chain.old j) = intervalCovariance Z c ((carrier L k).terminal p) (initialTerminal L k p) := by
  induction chain with
  | root p f =>
    change (∑ j : Fin 0, _) = intervalCovariance Z c (L.terminal p) (L.terminal p)
    simp only [Fin.sum_univ_zero, interval_same]
  | step k p f g prev ht old residual ho hr hcov d hd hrg ih =>
    obtain ⟨hprev, he, _, _⟩ := hp
    rw [Fin.sum_univ_succ]
    change old + (∑ j, prev.old j) = _
    rw [he, ih hprev]
    exact interval_add_adjacent Z hZ c hc hM hb ((carrier L k).nodeTime_mem p).2 (terminal_le_initial L k p.1)

/-- All old and residual intervals telescope to the original complete
covered covariance, in the same final observation space. -/
theorem Physical.sum_full (Z : Fin N → Observation) (hZ : ∀ i, (Z i).stop ≤ (Z i).target)
    (c : Domain → ℝ) (hc : Measurable c) {ell : ℝ} (hell : 0 < ell)
    (hb : ∀ p, ell ≤ c p ∧ c p ≤ R.reference p)
    {k : ℕ} {p : History P k} {g : Fin (n+k) → Fin N} (chain : Chain L k p g)
    (hp : Physical L Z c chain) :
    (∑ j, (chain.old j + chain.residual j)) =
      intervalCovariance Z R.reference ((carrier L k).terminal p) (initialTerminal L k p) := by
  have hc0 (z : Domain) : 0 ≤ c z ∧ c z ≤ R.upper :=
    ⟨hell.le.trans (hb z).1, (hb z).2.trans ((le_abs_self _).trans (R.reference_bound z))⟩
  have hr0 (z : Domain) : 0 ≤ R.reference z - c z ∧ R.reference z - c z ≤ R.upper :=
    ⟨sub_nonneg.mpr (hb z).2, (sub_le_self _ (hc0 z).1).trans ((le_abs_self _).trans (R.reference_bound z))⟩
  induction chain with
  | root p f =>
    change (∑ j : Fin 0, _) = intervalCovariance Z R.reference (L.terminal p) (L.terminal p)
    simp only [Fin.sum_univ_zero, interval_same]
  | step k p f g prev ht old residual ho hr hcov d hd hrg ih =>
    obtain ⟨hprev, he, hb', _⟩ := hp
    rw [Fin.sum_univ_succ]
    change old + residual + (∑ j, (prev.old j + prev.residual j)) = _
    rw [he, hb', ih hprev]
    have hs := interval_add_profiles Z hZ c (fun p => R.reference p - c p) hc (R.reference_measurable.sub hc)
      R.upper_nonneg R.upper_nonneg
      (fun z => by rw [abs_of_nonneg (hc0 z).1]; exact (hc0 z).2)
      (fun z => by rw [abs_of_nonneg (hr0 z).1]; exact (hr0 z).2)
      ((carrier L k).nodeTime p) ((carrier L k).terminal p.1)
    have hs' : intervalCovariance Z c ((carrier L k).nodeTime p) ((carrier L k).terminal p.1) +
        intervalCovariance Z (fun p => R.reference p - c p) ((carrier L k).nodeTime p) ((carrier L k).terminal p.1) =
        intervalCovariance Z R.reference ((carrier L k).nodeTime p) ((carrier L k).terminal p.1) := by
      simpa only [add_sub_cancel] using hs.symm
    rw [hs']
    exact interval_add_adjacent Z hZ R.reference R.reference_measurable R.upper_nonneg R.reference_bound
      ((carrier L k).nodeTime_mem p).2 (terminal_le_initial L k p.1)

def outsideProfile (c : Domain → ℝ) (lo hi : ℝ) (p : Domain) : ℝ := c p - intervalProfile c lo hi p

theorem outsideProfile_measurable (c : Domain → ℝ) (hc : Measurable c) (lo hi : ℝ) :
    Measurable (outsideProfile c lo hi) := hc.sub (measurable_intervalProfile hc lo hi)

theorem outsideProfile_bounds (c : Domain → ℝ) {M : ℝ} (hc : ∀ p, 0 ≤ c p ∧ c p ≤ M)
    (lo hi : ℝ) (p : Domain) : 0 ≤ outsideProfile c lo hi p ∧ outsideProfile c lo hi p ≤ M := by
  by_cases hp : p ∈ timeSet lo hi
  · simp only [outsideProfile, intervalProfile, Set.indicator_of_mem hp, sub_self]
    exact ⟨le_rfl, (hc p).1.trans (hc p).2⟩
  · simpa only [outsideProfile, intervalProfile, Set.indicator_of_notMem hp, sub_zero] using hc p

/-- Literal full stopped covariance coherence. The untouched initial
Gaussian covariance is the actual profile outside the covered intervals;
adding every old/residual pair gives precisely the full original law. -/
theorem Physical.full_covariance (Z : Fin N → Observation) (hZ : ∀ i, (Z i).stop ≤ (Z i).target)
    (c : Domain → ℝ) (hc : Measurable c) {ell : ℝ} (hell : 0 < ell)
    (hb : ∀ p, ell ≤ c p ∧ c p ≤ R.reference p)
    {k : ℕ} {p : History P k} {g : Fin (n+k) → Fin N} (chain : Chain L k p g)
    (hp : Physical L Z c chain) :
    StoppedGaussianFeatures.stoppedCovariance (fun i => (Z i).stop) (fun i => (Z i).target)
      (fun i => (Z i).center) (outsideProfile R.reference ((carrier L k).terminal p) (initialTerminal L k p)) 0 +
      (∑ j, (chain.old j + chain.residual j)) =
    StoppedGaussianFeatures.stoppedCovariance (fun i => (Z i).stop) (fun i => (Z i).target)
      (fun i => (Z i).center) R.reference 0 := by
  rw [Physical.sum_full L Z hZ c hc hell hb chain hp]
  let lo := (carrier L k).terminal p
  let hi := initialTerminal L k p
  have hcb (z : Domain) : 0 ≤ R.reference z ∧ R.reference z ≤ R.upper :=
    ⟨R.reference_nonneg z, (le_abs_self _).trans (R.reference_bound z)⟩
  have hout (z : Domain) : |outsideProfile R.reference lo hi z| ≤ R.upper := by
    rw [abs_of_nonneg (outsideProfile_bounds R.reference hcb lo hi z).1]
    exact (outsideProfile_bounds R.reference hcb lo hi z).2
  have he := StoppedCovarianceSplit.covariance_add (fun i => (Z i).stop) (fun i => (Z i).target)
    (fun i => (Z i).center) hZ 0 (outsideProfile_measurable R.reference R.reference_measurable lo hi)
    (measurable_intervalProfile R.reference_measurable lo hi)
    hout
    (profile_bound R.reference R.upper_nonneg R.reference_bound lo hi)
  have hsum : (fun z => outsideProfile R.reference lo hi z + intervalProfile R.reference lo hi z) = R.reference := by
    funext z
    simp only [outsideProfile, sub_add_cancel]
  rw [hsum] at he
  exact he.symm

end SHE.PhysicalScoreChain
