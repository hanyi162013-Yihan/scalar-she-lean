module

public import SHEStochastic.BorelObservablePath
public import SHEStochastic.AdaptedCanonicalPathTests
public import SHEStochastic.ContinuousNormExit
public import SHE.NullCompleteFiltration

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.BorelObservableStopping
open MeasureTheory ProbabilityTheory StoppedPathPasting StoppedPathExitRecovery AdaptedCanonicalPathTests
open scoped NNReal

local instance (H : ℝ≥0) : Fact ((0 : ℝ) ≤ H) := ⟨H.property⟩

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [CompleteSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

/-- A Borel nonnegative state observable defines a genuine stopping
time when it is continuous along the given adapted trajectories. The
observable need not be continuous on the whole state space. -/
theorem isStoppingTime (H : ℝ≥0) (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (X : Ω → Path H E) (a : E → ℝ) (ha : Measurable a)
    (ha0 : ∀ ω t, 0 ≤ a (X ω t))
    (hadapt : ∀ t : Time H, Measurable[F (toNN H t)] (fun ω ↦ X ω t))
    (hc : ∀ ω, Continuous (fun t ↦ a (X ω t))) (N : ℕ) :
    IsStoppingTime F (fun ω ↦ (toNN H (BorelObservablePath.exit H a N (X ω)) : WithTop ℝ≥0)) := by
  let A (q : ℝ≥0) (ω : Ω) := a (X ω (clock H q))
  have hAc (ω : Ω) : Continuous (fun q ↦ A q ω) := (hc ω).comp (continuous_clock H)
  have hAa : StronglyAdapted F A := by
    intro q
    exact ((ha.comp (hadapt (clock H q))).mono
      (F.mono (show toNN H (clock H q) ≤ q from min_le_left _ _)) le_rfl).stronglyMeasurable
  have hstop := ContinuousNormExit.isStoppingTime A hAc F hAa N
  intro q
  by_cases hH : H ≤ q
  · have he : {ω | (toNN H (BorelObservablePath.exit H a N (X ω)) : WithTop ℝ≥0) ≤ q} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, WithTop.coe_le_coe]
      exact (show toNN H (BorelObservablePath.exit H a N (X ω)) ≤ H from
        (BorelObservablePath.exit H a N (X ω)).property.2).trans hH
    rw [he]
    exact MeasurableSet.univ
  · have hq : q < H := lt_of_not_ge hH
    let t : Time H := ⟨q, q.property, by exact_mod_cast hq.le⟩
    have ht : t < ⊤ := by
      change (q : ℝ) < H
      exact_mod_cast hq
    have he : {ω | (toNN H (BorelObservablePath.exit H a N (X ω)) : WithTop ℝ≥0) ≤ q} =
        {ω | ContinuousNormExit.exit A N ω ≤ q} := by
      ext ω
      simp only [Set.mem_setOf_eq, WithTop.coe_le_coe]
      change (BorelObservablePath.exit H a N (X ω) ≤ t) ↔ _
      rw [BorelObservablePath.exit_eq H a N (X ω) (hc ω),
        time_le_iff_of_lt_top H a N (X ω) (isClosed_le continuous_const (hc ω)) t ht,
        ContinuousNormExit.le_iff A hAc N q ω]
      constructor
      · rintro ⟨s, hs, hh⟩
        refine ⟨toNN H s, ⟨bot_le, hs⟩, ?_⟩
        simpa only [A, clock_toNN, Real.norm_eq_abs, abs_of_nonneg (ha0 ω s)] using hh
      · rintro ⟨s, hs, hh⟩
        have hsH : s ≤ H := hs.2.trans hq.le
        refine ⟨clock H s, ?_, ?_⟩
        · change min (s : ℝ) (H : ℝ) ≤ (q : ℝ)
          exact (min_le_left _ _).trans hs.2
        · simpa only [A, Real.norm_eq_abs, abs_of_nonneg (ha0 ω (clock H s))] using hh
    rw [he]
    exact hstop q

/-- Almost-sure scalar norm continuity is enough in a null-complete
filtration. The reconstructed observable is continuous everywhere; its
adaptation follows from equality with the actual state observable on a
single full-measure event. Its Borel exit is unchanged even on bad paths. -/
theorem isStoppingTime_of_ae_continuous (H : ℝ≥0) (μ : Measure Ω)
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (hnull : SHE.NullCompleteFiltration.ContainsNullSets F μ)
    (X : Ω → Path H E) (a : E → ℝ) (ha : Measurable a)
    (ha0 : ∀ ω t, 0 ≤ a (X ω t))
    (hadapt : ∀ t : Time H, Measurable[F (toNN H t)] (fun ω ↦ X ω t))
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t ↦ a (X ω t))) (N : ℕ) :
    IsStoppingTime F (fun ω ↦ (toNN H (BorelObservablePath.exit H a N (X ω)) : WithTop ℝ≥0)) := by
  let Q (ω : Ω) := BorelObservablePath.observable H a (X ω)
  have hQa (t : Time H) : Measurable[F (toNN H t)] (fun ω ↦ Q ω t) := by
    apply StronglyMeasurable.measurable
    apply SHE.NullCompleteFiltration.stronglyMeasurable_congr F μ hnull (toNN H t)
      ((ha.comp (hadapt t)).stronglyMeasurable)
    filter_upwards [hc] with ω hω
    change BorelObservablePath.observable H a (X ω) t = a (X ω t)
    rw [BorelObservablePath.observable_eq H a (X ω) hω]
    rfl
  have hh := isStoppingTime H F Q id measurable_id
    (fun ω t ↦ BorelObservablePath.observable_nonneg H a (X ω) (ha0 ω) t) hQa
    (fun ω ↦ (Q ω).continuous) N
  have he (ω : Ω) : BorelObservablePath.exit H id N (Q ω) = BorelObservablePath.exit H a N (X ω) :=
    BorelObservablePath.exit_eq H id N (Q ω) (Q ω).continuous
  simpa only [he] using hh

end SHEStochastic.BorelObservableStopping
