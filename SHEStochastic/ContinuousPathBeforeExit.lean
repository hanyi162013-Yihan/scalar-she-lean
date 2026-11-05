module

public import SHEStochastic.ContinuousEqualityBeforeExit
public import SHEStochastic.AdaptedCanonicalPathTests

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.ContinuousPathBeforeExit
open MeasureTheory StoppedPathPasting AdaptedCanonicalPathTests
open scoped NNReal

/-- One continuous pre-exit path identity extends to the closed exit
and to the terminal horizon. Arbitrary finite or infinite exits are
allowed, and only the initial equality handles a possible zero exit. -/
theorem closed {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E]
    (μ : Measure Ω) (H : ℝ≥0) (X Y : Ω → Path H E) (τ : Ω → WithTop ℝ≥0)
    (hzero : ∀ᵐ ω ∂μ,X ω (origin H)=Y ω (origin H))
    (he : ∀ᵐ ω ∂μ,∀ t : Time H,(toNN H t : WithTop ℝ≥0)<τ ω → X ω t=Y ω t) :
    ∀ᵐ ω ∂μ,∀ t : Time H,(toNN H t : WithTop ℝ≥0)≤τ ω → X ω t=Y ω t := by
  have hc (Z : Ω → Path H E) : ∀ᵐ ω ∂μ,Continuous (fun t => Z ω (clock H t)) :=
    Filter.Eventually.of_forall (fun ω => (Z ω).continuous.comp (continuous_clock H))
  have hz : (fun ω => X ω (clock H 0))=ᵐ[μ] (fun ω => Y ω (clock H 0)) := by
    have hclock : clock H 0=origin H := by
      apply Subtype.ext
      simp only [clock,NNReal.coe_zero,min_eq_left H.coe_nonneg,origin]
    filter_upwards [hzero] with ω hω
    change X ω (clock H 0)=Y ω (clock H 0)
    rw [hclock]
    exact hω
  have hi (t : ℝ≥0) (ht : t<H) : ∀ᵐ ω ∂μ,(t : WithTop ℝ≥0)<τ ω → X ω (clock H t)=Y ω (clock H t) := by
    filter_upwards [he] with ω hω hτ
    apply hω (clock H t)
    have hct : toNN H (clock H t)=t := by
      apply NNReal.eq
      exact min_eq_left (show (t : ℝ)≤H from ht.le)
    rw [hct]
    exact hτ
  have hh := ContinuousEqualityBeforeExit.simultaneous_horizon μ
    (fun t ω => X ω (clock H t)) (fun t ω => Y ω (clock H t)) H τ (hc X) (hc Y) hz hi
  filter_upwards [hh] with ω hω t hτ
  let s : ℝ≥0 := toNN H t
  have hsH : s≤H := t.property.2
  have hs : clock H s=t := by
    apply Subtype.ext
    exact min_eq_left t.property.2
  simpa only [hs] using hω s hsH hτ

end SHEStochastic.ContinuousPathBeforeExit
