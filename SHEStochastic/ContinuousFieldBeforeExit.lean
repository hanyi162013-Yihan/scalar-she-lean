module

public import SHEStochastic.ContinuousEqualityBeforeExit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.ContinuousFieldBeforeExit
open MeasureTheory TopologicalSpace
open scoped NNReal

/-- A continuous parameter field has one common pre-exit equality
event, also for an infinite-valued random exit. The clock may depend
on several parameters, as in the actual heat time-space field. -/
theorem simultaneous {Ω A E : Type*} [MeasurableSpace Ω] [TopologicalSpace A] [SeparableSpace A]
    [MetricSpace E] (μ : Measure Ω) (X Y : A → Ω → E)
    (H : ℝ≥0) (τ : Ω → WithTop ℝ≥0) (clock : A → ℝ≥0) (hclock : Continuous clock)
    (hbound : ∀ p,clock p≤H)
    (hcX : ∀ᵐ ω ∂μ,Continuous (fun p => X p ω)) (hcY : ∀ᵐ ω ∂μ,Continuous (fun p => Y p ω))
    (he : ∀ p,∀ᵐ ω ∂μ,(clock p : WithTop ℝ≥0)<τ ω → X p ω=Y p ω) :
    ∀ᵐ ω ∂μ,∀ p,(clock p : WithTop ℝ≥0)<τ ω → X p ω=Y p ω := by
  let σ := fun ω => min ((H+1 : ℝ≥0) : WithTop ℝ≥0) (τ ω)
  have hne (ω : Ω) : σ ω≠⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  let r := fun ω => (σ ω).untopA
  have hh := ContinuousEqualityBeforeExit.simultaneous_clock μ X Y (fun ω => (r ω : ℝ))
    (fun p => (clock p : ℝ)) (continuous_subtype_val.comp hclock) hcX hcY (fun p => by
      filter_upwards [he p] with ω hω hp
      apply hω
      have hpr : clock p<r ω := by exact_mod_cast hp
      exact ((WithTop.lt_untopA_iff (hne ω)).mp hpr).trans_le (min_le_right _ _))
  filter_upwards [hh] with ω hω p hp
  apply hω p
  have hb : clock p<H+1 := (hbound p).trans_lt (by simp)
  have hpr : clock p<r ω := (WithTop.lt_untopA_iff (hne ω)).mpr
    (lt_min (by exact_mod_cast hb) hp)
  exact_mod_cast hpr

end SHEStochastic.ContinuousFieldBeforeExit
