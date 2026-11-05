module

public import MathFin.Foundations.ExitTime
public import Mathlib.MeasureTheory.Measure.Continuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.ContinuousNormExit
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  (U : ℝ≥0 → Ω → E) (hc : ∀ ω, Continuous (fun t ↦ U t ω))

/-- First closed norm-level exit, using the public continuous-process
exit construction. In particular E may be the spatial L² state space. -/
def exit (N : ℕ) : Ω → WithTop ℝ≥0 := MathFin.exitTime (fun t ω ↦ ‖U t ω‖) N

include hc

theorem le_iff (N : ℕ) (t : ℝ≥0) (ω : Ω) :
    exit U N ω ≤ (t : WithTop ℝ≥0) ↔ ∃ s ∈ Icc (0 : ℝ≥0) t, (N : ℝ) ≤ ‖U s ω‖ := by
  simpa only [exit, abs_of_nonneg (norm_nonneg _)] using
    MathFin.exitTime_le_iff (fun ω ↦ (hc ω).norm) N t ω

theorem before_bound (N : ℕ) (t : ℝ≥0) (ω : Ω) (ht : (t : WithTop ℝ≥0) < exit U N ω) :
    ‖U t ω‖ < N := by
  by_contra hn
  exact (not_le_of_gt ht) ((le_iff U hc N t ω).mpr ⟨t, ⟨zero_le, le_rfl⟩, le_of_not_gt hn⟩)

/-- The public rational characterization gives a stopping time for any
filtration to which U is strongly adapted; no right-continuity is added. -/
theorem isStoppingTime (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (ha : StronglyAdapted F U) (N : ℕ) : IsStoppingTime F (exit U N) := by
  intro i
  have hset : {ω | exit U N ω ≤ (i : WithTop ℝ≥0)} =
      ⋂ m : ℕ, ⋃ q : {q : ℚ // Real.toNNReal q ≤ i},
        {ω | (N : ℝ) - 1 / (m + 1) ≤ ‖U (Real.toNNReal (q : ℚ)) ω‖} := by
    ext ω
    simp only [mem_setOf_eq, mem_iInter, mem_iUnion, Subtype.exists, exists_prop]
    rw [exit, MathFin.exitTime_le_iff (fun ω ↦ (hc ω).norm),
      MathFin.exists_le_abs_eq_iInter_iUnion (fun ω ↦ (hc ω).norm)]
    simp only [abs_of_nonneg (norm_nonneg _)]
  rw [hset]
  apply MeasurableSet.iInter
  intro m
  apply MeasurableSet.iUnion
  intro q
  exact measurableSet_le measurable_const (((ha (Real.toNNReal (q : ℚ))).norm.measurable).mono
    (F.mono q.property) le_rfl)

theorem monotone (ω : Ω) : Monotone (fun N ↦ exit U N ω) :=
  MathFin.exitTime_monotone (fun ω ↦ (hc ω).norm) ω

theorem tendsto_top (ω : Ω) : Tendsto (fun N ↦ exit U N ω) atTop (𝓝 ⊤) :=
  MathFin.exitTime_tendsto_top (fun ω ↦ (hc ω).norm) ω

/-- Exit probabilities vanish on each fixed horizon, without a global
supremum-moment assumption. Compact continuity supplies pathwise escape. -/
theorem probability_vanishes (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (ha : StronglyAdapted F U) (H : ℝ≥0) :
    Tendsto (fun N ↦ μ {ω | exit U N ω ≤ (H : WithTop ℝ≥0)}) atTop (𝓝 0) := by
  let bad (N : ℕ) : Set Ω := {ω | exit U N ω ≤ (H : WithTop ℝ≥0)}
  have hm (N : ℕ) : MeasurableSet (bad N) := (F.le H) _ (isStoppingTime U hc F ha N H)
  have hanti : Antitone bad := fun N M hNM ω hω ↦ (monotone U hc ω hNM).trans hω
  have he : (⋂ N, bad N) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    have htop := tendsto_top U hc ω
    rw [WithTop.tendsto_nhds_top_iff] at htop
    obtain ⟨N, hN⟩ := (htop H).exists
    exact (not_le_of_gt hN) (mem_iInter.mp hω N)
  have ht := tendsto_measure_iInter_atTop (μ := μ) (fun N ↦ (hm N).nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  simp only [he, measure_empty] at ht
  convert ht using 1 <;> rfl

end SHEStochastic.ContinuousNormExit
