module

public import SHE.ControlledStoppedLeaf

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
noncomputable section

namespace SHE.FutureWindowDomination
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement StoppedGaussianFeatures
  StoppedFourier GaussianAssignmentBlocks OldIntervalCovariance
open scoped BigOperators
local instance : Fact (0<2*π) := ⟨by positivity⟩
variable {n : ℕ}

def timeSet (q : ℝ) : Set Domain := Ici q ×ˢ univ

def profile (c : Domain → ℝ) (q : ℝ) : Domain → ℝ := (timeSet q).indicator c

theorem profile_measurable {c : Domain → ℝ} (hc : Measurable c) (q : ℝ) :
    Measurable (profile c q) := hc.indicator (measurableSet_Ici.prod MeasurableSet.univ)

theorem historyMeasure_eq_restrict {q : ℝ} (hq : 0≤q) :
    historyMeasure q=(historyMeasure 0).restrict (timeSet q) := by
  unfold historyMeasure timeSet
  rw [← Measure.restrict_prod_eq_prod_univ,Measure.restrict_restrict measurableSet_Ici]
  congr 2
  exact (inter_eq_left.mpr (show Ici q⊆Ici 0 from fun r hr => hq.trans hr)).symm

/-- Changing the lower history endpoint is literally restriction of the
coefficient on the original product history space, including stopped rows. -/
theorem covariance_eq (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (c : Domain→ℝ) {q : ℝ} (hq : 0≤q) :
    stoppedCovariance σ target center (profile c q) 0=stoppedCovariance σ target center c q := by
  ext i j
  unfold StoppedGaussianFeatures.stoppedCovariance
  have he : (fun p : Domain => profile c q p*stoppedRow σ target center p i*
      stoppedRow σ target center p j) = (timeSet q).indicator
      (fun p => c p*stoppedRow σ target center p i*stoppedRow σ target center p j) := by
    funext p
    by_cases hp : p∈timeSet q
    · simp only [profile,indicator_of_mem hp]
    · simp only [profile,indicator_of_notMem hp,zero_mul]
  have hset : MeasurableSet (timeSet q) := measurableSet_Ici.prod MeasurableSet.univ
  rw [he,integral_indicator hset,←historyMeasure_eq_restrict hq]

/-- Removing the pre-q history leaves a positive covariance increment.
No common stopping time or nonsingular covariance is assumed. -/
theorem difference_posSemidef (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hages : ∀ i,σ i≤target i) (c : Domain→ℝ) (hc : Measurable c)
    {M : ℝ} (hb : ∀ p,0≤c p ∧ c p≤M) {q : ℝ} (hq : 0≤q) :
    (stoppedCovariance σ target center c 0-stoppedCovariance σ target center c q).PosSemidef := by
  have hwindow (p : Domain) : |profile c q p|≤M := by
    by_cases hp : p∈timeSet q
    · simpa only [profile,indicator_of_mem hp,abs_of_nonneg (hb p).1] using (hb p).2
    · simp only [profile,indicator_of_notMem hp,abs_zero]
      exact (hb p).1.trans (hb p).2
  have hcabs (p : Domain) : |c p|≤M := by rw [abs_of_nonneg (hb p).1];exact (hb p).2
  rw [←covariance_eq σ target center c hq,
    ←StoppedCovarianceSplit.covariance_sub σ target center hages 0 hc (profile_measurable hc q) hcabs hwindow]
  apply StoppedCovarianceSplit.covariance_posSemidef σ target center hages 0
    (M:=M) (hc.sub (profile_measurable hc q))
  intro p
  change 0≤c p-profile c q p ∧ c p-profile c q p≤M
  by_cases hp : p∈timeSet q
  · simp only [profile,indicator_of_mem hp,sub_self,le_refl,true_and]
    exact (hb p).1.trans (hb p).2
  · simpa only [profile,indicator_of_notMem hp,sub_zero] using hb p

theorem diagonal_le (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hages : ∀ i,σ i≤target i) (c : Domain→ℝ) (hc : Measurable c)
    {M : ℝ} (hb : ∀ p,0≤c p ∧ c p≤M) {q : ℝ} (hq : 0≤q) (i : Fin n) :
    stoppedCovariance σ target center c q i i≤stoppedCovariance σ target center c 0 i i := by
  have hh := (difference_posSemidef σ target center hages c hc hb hq).diag_nonneg (i:=i)
  change 0≤stoppedCovariance σ target center c 0 i i-stoppedCovariance σ target center c q i i at hh
  linarith

/-- An old interval lying after q is unchanged when viewed inside the
q-window. This is a literal equality of the interval coefficients. -/
theorem interval_covariance_eq (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (c : Domain→ℝ) {q lo hi : ℝ} (hq : 0≤q) (hlo : q≤lo) :
    stoppedCovariance σ target center (intervalProfile c lo hi) q=
      stoppedCovariance σ target center (intervalProfile c lo hi) 0 := by
  rw [←covariance_eq σ target center (intervalProfile c lo hi) hq]
  congr 1
  funext p
  by_cases hp : p∈OldIntervalCovariance.timeSet lo hi
  · have hw : p∈timeSet q := ⟨hlo.trans hp.1.1.le,mem_univ _⟩
    simp only [profile,indicator_of_mem hw]
  · simp only [intervalProfile,indicator_of_notMem hp]
    by_cases hw : p∈timeSet q <;> simp [profile,hw,hp]

end SHE.FutureWindowDomination
