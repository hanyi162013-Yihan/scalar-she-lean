module

public import SHE.OldIntervalRange
public import SHE.UniformScoreConstants
public import SHE.StoppedCovarianceOrder

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.UniformOldIntervalScores
open Set Filter MeasureTheory AddCircle Real StoppedFourier StoppedGaussianFeatures OldIntervalCovariance
  GaussianIncrement MeasurableGaussianScores
open scoped BigOperators
local instance uniformOldIntervalScores_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {ι : Type*} {n : ℕ}

/-- Every bounded elliptic old covariance dominates the SAME constant
floor covariance. This statement includes the zero profile outside the
old interval, rather than pretending it is globally elliptic. -/
theorem interval_range_and_score (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hages : ∀ i,σ i ≤ target i) (lo hi : ℝ) (c : Domain→ℝ) (hc : Measurable c)
    {ell M : ℝ} (hell : 0<ell) (hb : ∀ p,ell ≤ c p ∧ c p ≤ M)
    (D : State n) (hD : D∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (stoppedCovariance σ target center (intervalProfile (fun _=>ell) lo hi) 0)).range) :
    D∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (stoppedCovariance σ target center (intervalProfile c lo hi) 0)).range ∧
      scoreVariance (stoppedCovariance σ target center (intervalProfile c lo hi) 0) D ≤ 
        scoreVariance (stoppedCovariance σ target center (intervalProfile (fun _=>ell) lo hi) 0) D := by
  have hc0 : Measurable (intervalProfile (fun _=>ell) lo hi) := measurable_intervalProfile measurable_const lo hi
  have hc1 := measurable_intervalProfile hc lo hi
  have hb0 (p : Domain) : 0 ≤ intervalProfile (fun _=>ell) lo hi p ∧
      intervalProfile (fun _=>ell) lo hi p ≤ ell := by
    by_cases hp : p∈timeSet lo hi
    · simp only [intervalProfile,Set.indicator_of_mem hp]; exact ⟨hell.le,le_rfl⟩
    · simp only [intervalProfile,Set.indicator_of_notMem hp]; exact ⟨le_rfl,hell.le⟩
  have hb1 (p : Domain) : 0 ≤ intervalProfile c lo hi p ∧ intervalProfile c lo hi p ≤ max M 0 := by
    by_cases hp : p∈timeSet lo hi
    · simp only [intervalProfile,Set.indicator_of_mem hp]
      exact ⟨hell.le.trans (hb p).1,(hb p).2.trans (le_max_left _ _)⟩
    · simp only [intervalProfile,Set.indicator_of_notMem hp]
      exact ⟨le_rfl,le_max_right _ _⟩
  have hdom (p : Domain) : intervalProfile (fun _=>ell) lo hi p ≤ intervalProfile c lo hi p := by
    by_cases hp : p∈timeSet lo hi
    · simp only [intervalProfile,Set.indicator_of_mem hp]; exact (hb p).1
    · simp only [intervalProfile,Set.indicator_of_notMem hp]; exact le_rfl
  exact ⟨StoppedCovarianceOrder.range_mono σ target center hages 0 _ _ hc0 hc1 hb0 hb1 hdom hD,
    StoppedCovarianceOrder.scoreVariance_antitone σ target center hages 0 _ _ hc0 hc1 hb0 hb1 hdom hD⟩

/-- ONE genuine spatial event works for an arbitrary (even uncountable)
family of past-dependent old covariance profiles. The event is chosen
from the actual constant-floor covariance before the parameter enters. -/
theorem endpoint_all_profiles_ae (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i ≤ 1) (hages : ∀ i,σ i ≤ target i)
    {lo hi ell M : ℝ} (hlo : 0 ≤ lo) (hgap : lo<hi) (hstop : ∀ i,σ i ≤ lo ∨ hi ≤ σ i)
    (c : ι→Domain→ℝ) (hc : ∀ a,Measurable (c a)) (hell : 0<ell)
    (hb : ∀ a p,ell ≤ c a p ∧ c a p ≤ M) :
    ∀ᵐ x : HeatCircle ∂haarAddCircle,∀ a,
      stoppedRow σ target center (lo,x)∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
        (stoppedCovariance σ target center (intervalProfile (c a) lo hi) 0)).range ∧
      scoreVariance (stoppedCovariance σ target center (intervalProfile (c a) lo hi) 0)
          (stoppedRow σ target center (lo,x)) ≤ 
        scoreVariance (stoppedCovariance σ target center (intervalProfile (fun _=>ell) lo hi) 0)
          (stoppedRow σ target center (lo,x)) := by
  filter_upwards [endpoint_row_mem_range_ae σ target center hσ hσ1 hages hlo hgap hstop
    (fun _=>ell) measurable_const hell (fun _=>⟨le_rfl,le_rfl⟩)] with x hx
  intro a
  exact interval_range_and_score σ target center hages lo hi (c a) (hc a) hell (hb a) _ hx

/-- Full original active-parent heat localization on a common spatial
event for ALL varying reference profiles. No AE random-parameter
diagonal or independence is used. Dimensional witnesses are global. -/
theorem endpoint_heat_all_profiles_ae (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i ≤ 1) (hages : ∀ i,σ i ≤ target i)
    {lo hi ell M : ℝ} (hlo : 0 ≤ lo) (hgap : lo<hi) (hstop : ∀ i,σ i ≤ lo ∨ hi ≤ σ i)
    (hsmall : ∀ i,hi ≤ σ i→target i-lo ≤ UniformScoreConstants.horizon n)
    (c : ι→Domain→ℝ) (hc : ∀ a,Measurable (c a)) (hell : 0<ell)
    (hb : ∀ a p,ell ≤ c a p ∧ c a p ≤ M) :
    ∀ᵐ x : HeatCircle ∂haarAddCircle,∀ a,
      stoppedRow σ target center (lo,x)∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
        (stoppedCovariance σ target center (intervalProfile (c a) lo hi) 0)).range ∧
      scoreVariance (stoppedCovariance σ target center (intervalProfile (c a) lo hi) 0)
          (stoppedRow σ target center (lo,x)) ≤ 
        (UniformScoreConstants.constant n/(ell*(hi-lo)))*∑ i∈IntervalHistoryEnergy.active σ hi,
          ‖ProfileVariance.heatPhysical (2*(target i-lo)) (center i) x‖ := by
  filter_upwards [endpoint_all_profiles_ae σ target center hσ hσ1 hages hlo hgap hstop c hc hell hb,
    UniformScoreConstants.score_heat_kernel n σ target center hages hlo hgap hstop hsmall
      (fun _=>ell) measurable_const hell (fun _=>⟨le_rfl,le_rfl⟩)] with x hx hheat
  intro a
  exact ⟨(hx a).1,(hx a).2.trans hheat⟩

end SHE.UniformOldIntervalScores
