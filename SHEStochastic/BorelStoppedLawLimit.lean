module

public import SHEStochastic.BorelObservablePath
public import SHEStochastic.LocalizationLawLimit
public import SHEStochastic.UnboundedMomentBounds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.BorelStoppedLawLimit
open MeasureTheory StoppedPathPasting StoppedPathExitRecovery
open scoped NNReal Topology

local instance (H : ℝ≥0) : Fact ((0 : ℝ) ≤ H) := ⟨H.property⟩

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (H : ℝ≥0) (a : E → ℝ) (ha : Measurable a)

theorem stopped_eq_of_no_exit (R : ℝ) (x : Path H E)
    (hx : BorelObservablePath.exit H a R x = ⊤) : BorelObservablePath.stopped H a R x = x := by
  ext t
  change x (pastTime H (BorelObservablePath.exit H a R x) t) = x t
  rw [hx]
  congr 1
  apply Subtype.ext
  change min t.val (H : ℝ) = t.val
  exact min_eq_left t.property.2

include ha

/-- The exit event is contained in a tail event of a genuine measurable
continuous-path norm. Thus every original sample law has vanishing exit
probabilities, without an additional moment or tightness assumption. -/
theorem exit_probability_vanishes {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → Path H E) (hX : Measurable X) :
    Filter.Tendsto (fun n : ℕ ↦ μ {ω | BorelObservablePath.exit H a n (X ω) ≠ ⊤})
      Filter.atTop (nhds 0) := by
  let D (ω : Ω) := ‖BorelObservablePath.observable H a (X ω)‖
  have hD : Measurable D := ((BorelObservablePath.measurable_observable H a ha).comp hX).norm
  apply UnboundedMomentBounds.exit_vanishes μ D hD
  intro n ω hω
  have hh := attained H id n (BorelObservablePath.observable H a (X ω))
    (isClosed_le continuous_const (BorelObservablePath.observable H a (X ω)).continuous) hω
  exact hh.trans ((le_abs_self _).trans ((BorelObservablePath.observable H a (X ω)).norm_coe_le_norm _))

/-- Equality at every Borel localization implies equality of the FULL
original state-path laws. Exit tails are proved here from the observable
path norm; only the localized law comparison remains to be supplied. -/
theorem laws_eq_cofinal {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) [IsFiniteMeasure μ] (ν : Measure Ω') [IsFiniteMeasure ν]
    (X : Ω → Path H E) (Y : Ω' → Path H E) (hX : Measurable X) (hY : Measurable Y)
    (levels : ℕ → ℕ) (hlevels : Filter.Tendsto levels Filter.atTop Filter.atTop)
    (same : ∀ n : ℕ, μ.map (fun ω ↦ BorelObservablePath.stopped H a (levels n) (X ω)) =
      ν.map (fun ω ↦ BorelObservablePath.stopped H a (levels n) (Y ω))) : μ.map X = ν.map Y := by
  apply LocalizationLawLimit.laws_eq_of_localized X Y hX hY
    (fun n ω ↦ BorelObservablePath.stopped H a (levels n) (X ω))
    (fun n ω ↦ BorelObservablePath.stopped H a (levels n) (Y ω))
    (fun n ↦ (BorelObservablePath.measurable_stopped H a ha (levels n)).comp hX)
    (fun n ↦ (BorelObservablePath.measurable_stopped H a ha (levels n)).comp hY)
    (fun n ↦ {ω | BorelObservablePath.exit H a (levels n) (X ω) ≠ ⊤})
    (fun n ↦ {ω | BorelObservablePath.exit H a (levels n) (Y ω) ≠ ⊤})
  · intro n ω hω
    exact (stopped_eq_of_no_exit H a (levels n) (X ω) (Classical.not_not.mp hω)).symm
  · intro n ω hω
    exact (stopped_eq_of_no_exit H a (levels n) (Y ω) (Classical.not_not.mp hω)).symm
  · exact same
  · exact (exit_probability_vanishes H a ha μ X hX).comp hlevels
  · exact (exit_probability_vanishes H a ha ν Y hY).comp hlevels


/-- The natural-number cutoff sequence is a specialization of cofinal recovery. -/
theorem laws_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) [IsFiniteMeasure μ] (ν : Measure Ω') [IsFiniteMeasure ν]
    (X : Ω → Path H E) (Y : Ω' → Path H E) (hX : Measurable X) (hY : Measurable Y)
    (same : ∀ n : ℕ, μ.map (fun ω ↦ BorelObservablePath.stopped H a n (X ω)) =
      ν.map (fun ω ↦ BorelObservablePath.stopped H a n (Y ω))) : μ.map X = ν.map Y :=
  laws_eq_cofinal H a ha μ ν X Y hX hY id Filter.tendsto_id same

end SHEStochastic.BorelStoppedLawLimit
