module

public import SHEStochastic.StoppedPathPasting
public import BrownianMotion.Continuity.KolmogorovChentsov
public import Mathlib.Topology.Order.DenselyOrdered

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.ContinuousEqualityBeforeExit
open MeasureTheory ProbabilityTheory StoppedPathPasting TopologicalSpace
open scoped NNReal

/-- Fixed-time equality before a random exit becomes one simultaneous
pathwise equality on the open pre-exit interval. Multiplying the distance
by the continuous positive pre-exit weight allows direct reuse of the
public indistinguishability theorem. The state space may be vector-valued. -/
theorem simultaneous_clock {Ω E A : Type*} [MeasurableSpace Ω] [MetricSpace E]
    [TopologicalSpace A] [SeparableSpace A]
    (μ : Measure Ω) (X Y : A → Ω → E) (r : Ω → ℝ)
    (clock : A → ℝ) (hclock : Continuous clock)
    (hcX : ∀ᵐ ω ∂μ, Continuous (fun t ↦ X t ω))
    (hcY : ∀ᵐ ω ∂μ, Continuous (fun t ↦ Y t ω))
    (he : ∀ t : A, ∀ᵐ ω ∂μ, clock t < r ω → X t ω = Y t ω) :
    ∀ᵐ ω ∂μ, ∀ t : A, clock t < r ω → X t ω = Y t ω := by
  let D (t : A) (ω : Ω) : ℝ := max (r ω - clock t) 0 * dist (X t ω) (Y t ω)
  have hcD : ∀ᵐ ω ∂μ, Continuous (fun t ↦ D t ω) := by
    filter_upwards [hcX, hcY] with ω hx hy
    exact ((continuous_const.sub hclock).max continuous_const).mul (hx.dist hy)
  have hz (t : A) : ∀ᵐ ω ∂μ, D t ω = 0 := by
    filter_upwards [he t] with ω hω
    by_cases ht : clock t < r ω
    · simp only [D, hω ht, dist_self, mul_zero]
    · simp only [D, max_eq_right (sub_nonpos.mpr (le_of_not_gt ht)), zero_mul]
  have hh := indistinguishable_of_edist_modification hcD
    (Filter.Eventually.of_forall fun _ : Ω ↦ (continuous_const : Continuous (fun _ : A ↦ (0 : ℝ))))
    (fun t ↦ (hz t).mono fun ω hω ↦ by rw [hω, edist_self])
  exact hh.mono fun ω hω t ht ↦ by
    have hd : D t ω = 0 := edist_eq_zero.mp (hω t)
    have hp : 0 < max (r ω - clock t) 0 := lt_max_of_lt_left (sub_pos.mpr ht)
    exact dist_eq_zero.mp ((mul_eq_zero.mp hd).resolve_left hp.ne')

theorem simultaneous {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E]
    (H : ℝ≥0) (μ : Measure Ω) (X Y : Time H → Ω → E) (r : Ω → Time H)
    (hcX : ∀ᵐ ω ∂μ, Continuous (fun t ↦ X t ω))
    (hcY : ∀ᵐ ω ∂μ, Continuous (fun t ↦ Y t ω))
    (he : ∀ t : Time H, ∀ᵐ ω ∂μ, t.val < (r ω).val → X t ω = Y t ω) :
    ∀ᵐ ω ∂μ, ∀ t : Time H, t.val < (r ω).val → X t ω = Y t ω :=
  simultaneous_clock μ X Y (fun ω ↦ (r ω).val) Subtype.val continuous_subtype_val hcX hcY he

/-- A continuous pre-exit identity extends to the exit itself on one
common full-measure event. The initial identity also covers a zero exit. -/
theorem simultaneous_closed {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E]
    (μ : Measure Ω) (X Y : ℝ≥0 → Ω → E) (r : Ω → ℝ≥0)
    (hcX : ∀ᵐ ω ∂μ, Continuous (fun t ↦ X t ω))
    (hcY : ∀ᵐ ω ∂μ, Continuous (fun t ↦ Y t ω))
    (hzero : X 0 =ᵐ[μ] Y 0)
    (he : ∀ t, ∀ᵐ ω ∂μ, t < r ω → X t ω = Y t ω) :
    ∀ᵐ ω ∂μ, ∀ t, t ≤ r ω → X t ω = Y t ω := by
  have hh := simultaneous_clock μ X Y (fun ω ↦ (r ω : ℝ)) (fun t : ℝ≥0 ↦ (t : ℝ))
    continuous_subtype_val hcX hcY he
  filter_upwards [hh, hcX, hcY, hzero] with ω hω hx hy hz t ht
  by_cases hr : r ω = 0
  · have ht0 : t = 0 := le_antisymm (ht.trans_eq hr) zero_le
    simpa only [ht0] using hz
  · have hs : Set.Ico (0 : ℝ≥0) (r ω) ⊆ {s | X s ω = Y s ω} := fun s hs ↦ hω s hs.2
    have hclose := (isClosed_eq hx hy).closure_subset_iff.mpr hs
    rw [closure_Ico (Ne.symm hr)] at hclose
    exact hclose ⟨zero_le, ht⟩

theorem stopped_eq {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E]
    (μ : Measure Ω) (X Y : ℝ≥0 → Ω → E) (r : Ω → ℝ≥0)
    (hcX : ∀ᵐ ω ∂μ, Continuous (fun t ↦ X t ω))
    (hcY : ∀ᵐ ω ∂μ, Continuous (fun t ↦ Y t ω))
    (hzero : X 0 =ᵐ[μ] Y 0)
    (he : ∀ t, ∀ᵐ ω ∂μ, t < r ω → X t ω = Y t ω) :
    ∀ᵐ ω ∂μ, ∀ t, stoppedProcess X (fun ω ↦ (r ω : WithTop ℝ≥0)) t ω =
      stoppedProcess Y (fun ω ↦ (r ω : WithTop ℝ≥0)) t ω := by
  filter_upwards [simultaneous_closed μ X Y r hcX hcY hzero he] with ω hω t
  simp only [stoppedProcess, ← WithTop.coe_min,
    WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  exact hω (min t (r ω)) (min_le_right _ _)

/-- One common event covers a closed deterministic horizon and a
possibly infinite random exit. Only interior fixed-time identities
and the initial equality are needed. -/
theorem simultaneous_horizon {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E]
    (μ : Measure Ω) (X Y : ℝ≥0 → Ω → E) (H : ℝ≥0) (τ : Ω → WithTop ℝ≥0)
    (hcX : ∀ᵐ ω ∂μ, Continuous (fun t ↦ X t ω))
    (hcY : ∀ᵐ ω ∂μ, Continuous (fun t ↦ Y t ω))
    (hzero : X 0 =ᵐ[μ] Y 0)
    (he : ∀ t, t < H → ∀ᵐ ω ∂μ, (t : WithTop ℝ≥0) < τ ω → X t ω = Y t ω) :
    ∀ᵐ ω ∂μ, ∀ t, t ≤ H → (t : WithTop ℝ≥0) ≤ τ ω → X t ω = Y t ω := by
  let σ (ω : Ω) := min (H : WithTop ℝ≥0) (τ ω)
  let r (ω : Ω) : ℝ≥0 := (σ ω).untopA
  have hne (ω : Ω) : σ ω ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  have hi (t : ℝ≥0) : ∀ᵐ ω ∂μ, t < r ω → X t ω = Y t ω := by
    by_cases ht : t < H
    · filter_upwards [he t ht] with ω hω hr
      exact hω (((WithTop.lt_untopA_iff (hne ω)).mp hr).trans_le (min_le_right _ _))
    · apply Filter.Eventually.of_forall
      intro ω hr
      exact (ht (WithTop.coe_lt_coe.mp
        (((WithTop.lt_untopA_iff (hne ω)).mp hr).trans_le (min_le_left _ _)))).elim
  filter_upwards [simultaneous_closed μ X Y r hcX hcY hzero hi] with ω hω t ht hτ
  exact hω t ((WithTop.le_untopA_iff (hne ω)).mpr (le_min (by exact_mod_cast ht) hτ))

theorem stopped_eq_horizon {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E]
    (μ : Measure Ω) (X Y : ℝ≥0 → Ω → E) (H : ℝ≥0) (τ : Ω → WithTop ℝ≥0)
    (hcX : ∀ᵐ ω ∂μ, Continuous (fun t ↦ X t ω))
    (hcY : ∀ᵐ ω ∂μ, Continuous (fun t ↦ Y t ω))
    (hzero : X 0 =ᵐ[μ] Y 0)
    (he : ∀ t, t < H → ∀ᵐ ω ∂μ, (t : WithTop ℝ≥0) < τ ω → X t ω = Y t ω) :
    ∀ᵐ ω ∂μ, ∀ t, stoppedProcess X (fun ω ↦ min (H : WithTop ℝ≥0) (τ ω)) t ω =
      stoppedProcess Y (fun ω ↦ min (H : WithTop ℝ≥0) (τ ω)) t ω := by
  filter_upwards [simultaneous_horizon μ X Y H τ hcX hcY hzero he] with ω hω t
  let v := min (t : WithTop ℝ≥0) (min (H : WithTop ℝ≥0) (τ ω))
  have hne : v ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  let s : ℝ≥0 := v.untopA
  have hs : (s : WithTop ℝ≥0) = v := by
    rw [show s = v.untopA from rfl, WithTop.untopA_eq_untop hne, WithTop.coe_untop]
  have hsH : s ≤ H := WithTop.coe_le_coe.mp
    (hs.le.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsτ : (s : WithTop ℝ≥0) ≤ τ ω :=
    hs.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  exact hω s hsH hsτ

end SHEStochastic.ContinuousEqualityBeforeExit
