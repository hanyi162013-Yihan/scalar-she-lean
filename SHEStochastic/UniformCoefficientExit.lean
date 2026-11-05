module

public import SHEStochastic.BorelObservablePath
public import SHEStochastic.L2ExtendedUniformNorm
public import SHEStochastic.UnboundedCoefficientCutoff

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.UniformCoefficientExit
open MeasureTheory StoppedPathPasting StoppedPathExitRecovery
open scoped NNReal ENNReal

variable {X E V : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] (ν : Measure X) [IsFiniteMeasure ν]
  [MeasurableSpace (Lp E 2 ν)] [BorelSpace (Lp E 2 ν)]
  [SecondCountableTopology (Lp E 2 ν)]

local instance (H : ℝ≥0) : Fact ((0 : ℝ) ≤ H) := ⟨H.property⟩

/-- The actual uniform-norm exit, as a Borel functional of the L2
state path. On regular paths this is the usual first closed-level hit. -/
def exit (H R : ℝ≥0) (x : Path H (Lp E 2 ν)) : Time H :=
  BorelObservablePath.exit H (L2ExtendedUniformNorm.realValue ν) R x

theorem measurable_exit (H R : ℝ≥0) : Measurable (exit (E := E) ν H R) := by
  apply BorelObservablePath.measurable_exit H (L2ExtendedUniformNorm.realValue ν) ?_ R
  exact ENNReal.measurable_toReal.comp (L2ExtendedUniformNorm.lowerSemicontinuous ν).measurable

theorem before_bound (H R : ℝ≥0) (x : Path H (Lp E 2 ν))
    (hc : Continuous (fun t ↦ L2ExtendedUniformNorm.realValue ν (x t)))
    (hf : ∀ t, L2ExtendedUniformNorm.value ν (x t) ≠ ⊤)
    (t : Time H) (ht : t < exit ν H R x) :
    L2ExtendedUniformNorm.value ν (x t) ≤ ENNReal.ofReal R := by
  change t < BorelObservablePath.exit H (L2ExtendedUniformNorm.realValue ν) R x at ht
  rw [BorelObservablePath.exit_eq H _ R x hc] at ht
  have hb := before H (L2ExtendedUniformNorm.realValue ν) R x t ht
  rw [← ENNReal.ofReal_toReal (hf t)]
  exact ENNReal.ofReal_le_ofReal hb.le

/-- The original and truncated coefficients agree almost everywhere in
space before the actual solution's uniform-norm exit. This applies to
scalar or matrix-valued coefficients without a pointwise representative
of the L2 state. -/
theorem coefficient_agrees (H R : ℝ≥0) (x : Path H (Lp E 2 ν))
    (hc : Continuous (fun t ↦ L2ExtendedUniformNorm.realValue ν (x t)))
    (hf : ∀ t, L2ExtendedUniformNorm.value ν (x t) ≠ ⊤)
    (G : E → V) (t : Time H) (ht : t < exit ν H R x) :
    (fun a ↦ UnboundedCoefficientCutoff.coefficient G R (x t a)) =ᵐ[ν]
      fun a ↦ G (x t a) := by
  have hb := (L2ExtendedUniformNorm.le_ofReal_iff ν (x t) R R.property).mp
    (before_bound ν H R x hc hf t ht)
  filter_upwards [hb] with a ha
  exact UnboundedCoefficientCutoff.agrees G R ha

theorem positive (H R : ℝ≥0) (x : Path H (Lp E 2 ν))
    (hc : Continuous (fun t ↦ L2ExtendedUniformNorm.realValue ν (x t)))
    (hH : 0 < H) (h0 : L2ExtendedUniformNorm.realValue ν (x (origin H)) < R) :
    origin H < exit ν H R x := by
  unfold exit
  rw [BorelObservablePath.exit_eq H _ R x hc]
  exact StoppedPathExitRecovery.positive H _ R x hc hH h0

theorem bound_at_exit (H R : ℝ≥0) (x : Path H (Lp E 2 ν))
    (hc : Continuous (fun t ↦ L2ExtendedUniformNorm.realValue ν (x t)))
    (hf : ∀ t, L2ExtendedUniformNorm.value ν (x t) ≠ ⊤)
    (h0 : L2ExtendedUniformNorm.realValue ν (x (origin H)) ≤ R) :
    L2ExtendedUniformNorm.value ν (x (exit ν H R x)) ≤ ENNReal.ofReal (R : ℝ) := by
  have he : exit ν H R x = time H (L2ExtendedUniformNorm.realValue ν) R x :=
    BorelObservablePath.exit_eq H _ R x hc
  have hb := StoppedPathExitRecovery.at_exit_le H (L2ExtendedUniformNorm.realValue ν) R x hc h0
  rw [he, ← ENNReal.ofReal_toReal (hf _)]
  exact ENNReal.ofReal_le_ofReal hb

theorem before_or_at_bound (H R : ℝ≥0) (x : Path H (Lp E 2 ν))
    (hc : Continuous (fun t ↦ L2ExtendedUniformNorm.realValue ν (x t)))
    (hf : ∀ t, L2ExtendedUniformNorm.value ν (x t) ≠ ⊤)
    (h0 : L2ExtendedUniformNorm.realValue ν (x (origin H)) ≤ R)
    (t : Time H) (ht : t ≤ exit ν H R x) :
    L2ExtendedUniformNorm.value ν (x t) ≤ ENNReal.ofReal (R : ℝ) := by
  rcases ht.lt_or_eq with ht | ht
  · exact before_bound ν H R x hc hf t ht
  · rw [ht]
    exact bound_at_exit ν H R x hc hf h0

theorem attained (H R : ℝ≥0) (x : Path H (Lp E 2 ν))
    (hc : Continuous (fun t ↦ L2ExtendedUniformNorm.realValue ν (x t)))
    (hf : ∀ t, L2ExtendedUniformNorm.value ν (x t) ≠ ⊤)
    (h0 : L2ExtendedUniformNorm.realValue ν (x (origin H)) ≤ R)
    (hx : exit ν H R x ≠ ⊤) :
    L2ExtendedUniformNorm.value ν (x (exit ν H R x)) = ENNReal.ofReal R := by
  have he : exit ν H R x = time H (L2ExtendedUniformNorm.realValue ν) R x :=
    BorelObservablePath.exit_eq H _ R x hc
  rw [he] at hx ⊢
  rw [← ENNReal.ofReal_toReal (hf _)]
  exact congrArg ENNReal.ofReal (attained_eq H (L2ExtendedUniformNorm.realValue ν) R x hc h0 hx)

end SHEStochastic.UniformCoefficientExit
