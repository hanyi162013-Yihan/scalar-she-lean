module

public import SHEStochastic.ContinuousNormExit
public import SHE.PredictableTime

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarPredictableNormStop
open MeasureTheory Set SHE Filter
open scoped NNReal ENNReal Topology

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (W : ℝ≥0 → Ω → E)
  (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  (hc : ∀ ω,Continuous (fun t => W t ω))

include hc in
private theorem before_iff (N : ℕ) (t : ℝ≥0) (ω : Ω) :
    (t : WithTop ℝ≥0)<ContinuousNormExit.exit W N ω ↔
      (t : WithTop ℝ≥0)≤ContinuousNormExit.exit W N ω ∧ ‖W t ω‖<(N : ℝ) := by
  constructor
  · intro h
    exact ⟨h.le,ContinuousNormExit.before_bound W hc N t ω h⟩
  · rintro ⟨hle,hn⟩
    by_contra! hge
    obtain ⟨s,hs,hval⟩ := (ContinuousNormExit.le_iff W hc N t ω).mp hge
    have hts : t ≤ s := by
      have he := (ContinuousNormExit.le_iff W hc N s ω).mpr ⟨s,⟨zero_le,le_rfl⟩,hval⟩
      exact WithTop.coe_le_coe.mp (hle.trans he)
    have he := le_antisymm hts hs.2
    exact (not_le_of_gt hn) (he.symm ▸ hval)

private theorem gate_predictable (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime F τ) :
    MeasurableSet[F.predictable] {p : ℝ≥0×Ω | (p.1 : WithTop ℝ≥0)≤τ p.2} := by
  classical
  let V (t : ℝ≥0) (ω : Ω) : ℝ := if (t : WithTop ℝ≥0)≤τ ω then 1 else 0
  have hA : StronglyAdapted F V := by
    intro t
    exact (Measurable.ite (hτ.measurableSet_ge t) measurable_const measurable_const).stronglyMeasurable
  have hLeft (ω : Ω) (t : ℝ≥0) : ContinuousWithinAt (fun s => V s ω) (Iio t) t := by
    by_cases h : (t : WithTop ℝ≥0)≤τ ω
    · apply (continuousWithinAt_const (b := (1 : ℝ))).congr
      · intro s hs
        have hs' : (s : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0) :=
          WithTop.coe_le_coe.mpr (show s ≤ t from (show s < t from hs).le)
        exact ite_eq_left (hs'.trans h)
      · exact ite_eq_left h
    · have h' : τ ω < (t : WithTop ℝ≥0) := lt_of_not_ge h
      obtain ⟨v,hv⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt h')
      have hv' : v<t := WithTop.coe_lt_coe.mp (hv ▸ h')
      have he : (fun s => V s ω) =ᶠ[𝓝[Iio t] t] fun _ => (0 : ℝ) := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hv')] with s hs
        have hns : ¬(s : WithTop ℝ≥0)≤τ ω := by
          rw [←hv,WithTop.coe_le_coe]
          exact not_le_of_gt hs
        exact ite_eq_right hns
      apply continuousWithinAt_const.congr_of_eventuallyEq he
      exact ite_eq_right h
  have hp := hA.isStronglyPredictable_of_leftContinuous hLeft
  have hset := hp.measurable (measurableSet_singleton (1 : ℝ))
  convert hset using 1
  ext ⟨t,ω⟩
  change ((t : WithTop ℝ≥0)≤τ ω) ↔ V t ω=1
  by_cases h : (t : WithTop ℝ≥0)≤τ ω <;> simp [V]

include hW hc in
/-- The exact strict pre-exit region of the continuous original
state is predictable. It uses the actual spatial norm exit. -/
theorem predictable (N : ℕ) :
    MeasurableSet[F.predictable] {p : ℝ≥0×Ω | (p.1 : WithTop ℝ≥0)<ContinuousNormExit.exit W N p.2} := by
  have hτ := ContinuousNormExit.isStoppingTime W hc F (show IsStronglyPredictable F W from hW).stronglyAdapted N
  have hgate := gate_predictable F (ContinuousNormExit.exit W N) hτ
  have hnorm := measurableSet_lt hW.norm.measurable
    (measurable_const (a := (N : ℝ)))
  convert hgate.inter hnorm using 1
  ext ⟨t,ω⟩
  exact before_iff W hc N t ω

end SHEStochastic.ScalarPredictableNormStop
