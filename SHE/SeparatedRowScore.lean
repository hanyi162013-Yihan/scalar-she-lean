module

public import SHE.StoppedCovarianceOrder
public import SHE.PhysicalTerminalHeat

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.PhysicalFirstScore
open Set Filter MeasureTheory Real StoppedFourier WordRecursion StoppedGaussianFeatures
  OldIntervalCovariance PhysicalScoreChain MeasurableGaussianScores
open scoped BigOperators
local instance : Fact (0<2*π) := ⟨by positivity⟩
variable {n : ℕ}

theorem intervalProfile_nonnegative_bound (c : Domain→ℝ) {M : ℝ}
    (hb : ∀ p,0≤c p ∧ c p≤M) (lo hi : ℝ) (p : Domain) :
    0≤ intervalProfile c lo hi p ∧ intervalProfile c lo hi p≤M := by
  by_cases hp : p∈timeSet lo hi
  · simpa only [intervalProfile,Set.indicator_of_mem hp] using hb p
  · simp only [intervalProfile,Set.indicator_of_notMem hp,le_refl,true_and]
    exact (hb p).1.trans (hb p).2

theorem intervalProfile_mono_lower (c : Domain→ℝ) (hc : ∀ p,0≤c p)
    {q r hi : ℝ} (hqr : q≤r) (p : Domain) : intervalProfile c r hi p≤ intervalProfile c q hi p := by
  by_cases hp : p∈timeSet r hi
  · have hpq : p∈timeSet q hi := ⟨⟨hqr.trans_lt hp.1.1,hp.1.2⟩,hp.2⟩
    simp only [intervalProfile,Set.indicator_of_mem hp,Set.indicator_of_mem hpq,le_refl]
  · rw [intervalProfile,Set.indicator_of_notMem hp]
    by_cases hpq : p∈timeSet q hi
    · simpa only [intervalProfile,Set.indicator_of_mem hpq] using hc p
    · simp only [intervalProfile,Set.indicator_of_notMem hpq,le_refl]

theorem interval_range_mono_lower (Z : Fin n→Observation)
    (hages : ∀ i,(Z i).stop≤(Z i).target) (c : Domain→ℝ) (hc : Measurable c)
    {M q r hi : ℝ} (hb : ∀ p,0≤c p ∧ c p≤M) (hqr : q≤r) :
    (Matrix.toEuclideanCLM (𝕜:=ℝ) (intervalCovariance Z c r hi)).range≤
      (Matrix.toEuclideanCLM (𝕜:=ℝ) (intervalCovariance Z c q hi)).range := by
  exact StoppedCovarianceOrder.range_mono (fun i => (Z i).stop) (fun i => (Z i).target)
    (fun i => (Z i).center) hages 0 _ _ (measurable_intervalProfile hc r hi)
    (measurable_intervalProfile hc q hi) (intervalProfile_nonnegative_bound c hb r hi)
    (intervalProfile_nonnegative_bound c hb q hi) (intervalProfile_mono_lower c (fun p => (hb p).1) hqr)

theorem interval_score_antitone_lower (Z : Fin n→Observation)
    (hages : ∀ i,(Z i).stop≤(Z i).target) (c : Domain→ℝ) (hc : Measurable c)
    {M q r hi : ℝ} (hb : ∀ p,0≤c p ∧ c p≤M) (hqr : q≤r) {d : State n}
    (hd : d∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (intervalCovariance Z c r hi)).range) :
    scoreVariance (intervalCovariance Z c q hi) d≤scoreVariance (intervalCovariance Z c r hi) d := by
  exact StoppedCovarianceOrder.scoreVariance_antitone (fun i => (Z i).stop) (fun i => (Z i).target)
    (fun i => (Z i).center) hages 0 _ _ (measurable_intervalProfile hc r hi)
    (measurable_intervalProfile hc q hi) (intervalProfile_nonnegative_bound c hb r hi)
    (intervalProfile_nonnegative_bound c hb q hi) (intervalProfile_mono_lower c (fun p => (hb p).1) hqr) hd

/-- A later input heat row is a genuine direction for the ORIGINAL
q-window Gaussian. Its canonical inverse-score energy decreases when
the earlier part of that same covariance is restored. -/
theorem later_heatRow_range_score_ae (Z : Fin n→Observation)
    (hages : ∀ i,(Z i).stop≤(Z i).target) {q r hi ell M : ℝ}
    (hq : 0≤q) (hqr : q≤r) (hrhi : r<hi) (hhi : hi≤1) (hstop : ∀ i,hi≤(Z i).stop)
    (c : Domain→ℝ) (hc : Measurable c) (hell : 0<ell) (hb : ∀ p,ell≤c p ∧ c p≤M) :
    ∀ᵐ y : HeatCircle ∂AddCircle.haarAddCircle,
      heatRow Z r y∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (intervalCovariance Z c q hi)).range ∧
      scoreVariance (intervalCovariance Z c q hi) (heatRow Z r y)≤
        scoreVariance (intervalCovariance Z c r hi) (heatRow Z r y) := by
  have hcb (p : Domain) : 0≤c p ∧ c p≤M := ⟨hell.le.trans (hb p).1,(hb p).2⟩
  filter_upwards [terminal_heatRow_mem_range_ae Z (hq.trans hqr) hrhi hhi hstop hages c hc hell hb] with y hy
  exact ⟨interval_range_mono_lower Z hages c hc hcb hqr hy,
    interval_score_antitone_lower Z hages c hc hcb hqr hy⟩

/-- The full q-window first score in a later row-time r has the true
r-parent heat envelope, costing only the remaining reserved gap hi-r.
The Gaussian covariance and its current mean remain at q throughout. -/
theorem later_terminal_sqrt_heat_envelope (n : ℕ) :
    ∃ H C : ℝ,0<H ∧ 0<C ∧
    ∀ (Z : Fin n→Observation),(∀ i,(Z i).stop≤(Z i).target) →
    ∀ {q r hi ell M : ℝ},0≤q → q≤r → r<hi → hi≤1 → (∀ i,hi≤(Z i).stop) →
    (∀ i,(Z i).target-r≤H) →
    ∀ (c : Domain→ℝ),Measurable c → 0<ell → (∀ p,ell≤c p ∧ c p≤M) →
    ∀ᵐ y : HeatCircle ∂AddCircle.haarAddCircle,
      heatRow Z r y∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (intervalCovariance Z c q hi)).range ∧
      Real.sqrt (scoreVariance (intervalCovariance Z c q hi) (heatRow Z r y))≤
        Real.sqrt (C/(ell*(hi-r)))*
          ∑ i : Fin n,Real.sqrt ‖ProfileVariance.heatPhysical (4*((Z i).target-r)) (Z i).center y‖ := by
  obtain ⟨H,C,hH,hC,hV⟩ := terminal_sqrt_heat_envelope n
  refine ⟨H,C,hH,hC,?_⟩
  intro Z hages q r hi ell M hq hqr hrhi hhi hstop hsmall c hc hell hb
  filter_upwards [later_heatRow_range_score_ae Z hages hq hqr hrhi hhi hstop c hc hell hb,
    hV Z hages (hq.trans hqr) hrhi hstop hsmall c hc hell hb] with y hy henv
  exact ⟨hy.1,(Real.sqrt_le_sqrt hy.2).trans henv⟩

end SHE.PhysicalFirstScore
