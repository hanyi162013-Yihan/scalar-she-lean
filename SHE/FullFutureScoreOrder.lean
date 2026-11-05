module

public import SHE.StoppedCovarianceOrder
public import SHE.FutureWindowDomination

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
noncomputable section

namespace SHE.FullFutureScoreOrder
open Set MeasureTheory Real GaussianIncrement StoppedGaussianFeatures StoppedFourier
  MeasurableGaussianScores FutureWindowDomination StoppedCovarianceOrder
open scoped BigOperators
variable {n : ℕ}

theorem profile_bound (c : Domain→ℝ) {M : ℝ} (hb : ∀ p,0≤c p ∧ c p≤M) (q : ℝ) (p : Domain) :
    0≤profile c q p ∧ profile c q p≤M := by
  by_cases hp : p∈timeSet q
  · simpa only [profile,indicator_of_mem hp] using hb p
  · simp only [profile,indicator_of_notMem hp,le_refl,true_and]
    exact (hb p).1.trans (hb p).2

theorem profile_mono_lower (c : Domain→ℝ) (hc : ∀ p,0≤c p)
    {q r : ℝ} (hqr : q≤r) (p : Domain) : profile c r p≤profile c q p := by
  by_cases hp : p∈timeSet r
  · have hpq : p∈timeSet q := ⟨hqr.trans hp.1,hp.2⟩
    simp only [profile,indicator_of_mem hp,indicator_of_mem hpq,le_refl]
  · rw [profile,indicator_of_notMem hp]
    by_cases hpq : p∈timeSet q
    · simpa only [profile,indicator_of_mem hpq] using hc p
    · simp only [profile,indicator_of_notMem hpq,le_refl]

/-- Earlier full individually stopped future covariance contains the
entire later one, retaining every original stop and target. -/
theorem range_mono_lower (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hages : ∀ i,σ i≤target i) (c : Domain→ℝ) (hc : Measurable c)
    {M q r : ℝ} (hb : ∀ p,0≤c p ∧ c p≤M) (hq : 0≤q) (hqr : q≤r) :
    (Matrix.toEuclideanCLM (𝕜:=ℝ) (stoppedCovariance σ target center c r)).range≤
      (Matrix.toEuclideanCLM (𝕜:=ℝ) (stoppedCovariance σ target center c q)).range := by
  rw [←covariance_eq σ target center c (hq.trans hqr),←covariance_eq σ target center c hq]
  exact StoppedCovarianceOrder.range_mono σ target center hages 0 _ _
    (profile_measurable hc r) (profile_measurable hc q)
    (profile_bound c hb r) (profile_bound c hb q) (profile_mono_lower c (fun p=>(hb p).1) hqr)

theorem score_antitone_lower (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hages : ∀ i,σ i≤target i) (c : Domain→ℝ) (hc : Measurable c)
    {M q r : ℝ} (hb : ∀ p,0≤c p ∧ c p≤M) (hq : 0≤q) (hqr : q≤r)
    {d : State n} (hd : d∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (stoppedCovariance σ target center c r)).range) :
    scoreVariance (stoppedCovariance σ target center c q) d≤
      scoreVariance (stoppedCovariance σ target center c r) d := by
  rw [←covariance_eq σ target center c (hq.trans hqr)] at hd
  rw [←covariance_eq σ target center c (hq.trans hqr),←covariance_eq σ target center c hq]
  exact StoppedCovarianceOrder.scoreVariance_antitone σ target center hages 0 _ _
    (profile_measurable hc r) (profile_measurable hc q)
    (profile_bound c hb r) (profile_bound c hb q) (profile_mono_lower c (fun p=>(hb p).1) hqr) hd

end SHE.FullFutureScoreOrder
