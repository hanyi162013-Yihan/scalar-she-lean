module

public import SHEStochastic.CanonicalInitialKernel
public import SHEStochastic.ConditionalCountablePastTests
public import SHEStochastic.ConditionalIntegrablePastTests
public import SHE.CanonicalPastPathContinuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.CanonicalProcessTimeRegularity
open MeasureTheory ProbabilityTheory SHE SHE.DyadicApproximation SHE.FiniteHaar
open CanonicalStateDriverFiltration
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

variable {ι : Type*} [Countable ι] [DecidableEq ι] (H : ℝ≥0)

theorem continuous_clock : Continuous (clock H) :=
  (continuous_subtype_val.min continuous_const).subtype_mk _

theorem history (x : CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H) :
    Continuous (fun t ↦ CanonicalStateDriverFiltration.history H t x) := by
  have hs := (CanonicalPastPathContinuity.past_continuous H x none).fst
  have hd := continuous_pi fun i ↦ (CanonicalPastPathContinuity.past_continuous H x (some i)).snd
  exact (hs.prodMk hd).comp (continuous_clock H)

theorem fourier (a : ℂ →L[ℝ] ℝ) (n : ℤ) (x : CanonicalFourierFluctuation.Space (ι := ι) H) :
    Continuous (fun t ↦ CanonicalFourierFluctuation.value H a n t x) := by
  change Continuous (fun t : ℝ≥0 ↦ Real.exp ((min t H : ℝ≥0)*(n : ℝ)^2)*
    NativeFourierHeatCoordinate.coordinate a n (state H t x)-
      NativeFourierHeatCoordinate.coordinate a n (x.1 (StoppedPathPasting.origin H)))
  simp only [NNReal.coe_min]
  exact ((Real.continuous_exp.comp ((continuous_subtype_val.min continuous_const).mul_const _)).mul
    ((NativeFourierHeatCoordinate.coordinate a n).continuous.comp (state_continuous H x))).sub continuous_const

theorem fourier_clip (a : ℂ →L[ℝ] ℝ) (n : ℤ) (t : ℝ≥0) :
    CanonicalFourierFluctuation.value (ι := ι) H a n t = CanonicalFourierFluctuation.value H a n (min t H) := by
  funext x
  simp [CanonicalFourierFluctuation.value, clock, NNReal.coe_min, min_assoc, min_self]

theorem compensator (rate : ℝ) (hrate : 0 ≤ rate) (b : BoundedContinuousFunction E ℝ)
    (x : CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H) :
    Continuous (fun t ↦ CanonicalFourierCompensator.value H rate hrate b t x) :=
  (PathIntegratedCovariance.continuous_value H (PathIntegratedCovariance.exponential H rate hrate) b).comp
    (continuous_const.prodMk (continuous_clock H))

theorem compensator_clip (rate : ℝ) (hrate : 0 ≤ rate) (b : BoundedContinuousFunction E ℝ) (t : ℝ≥0) :
    CanonicalFourierCompensator.value (ι := ι) H rate hrate b t =
      CanonicalFourierCompensator.value H rate hrate b (min t H) := by
  funext x
  simp [CanonicalFourierCompensator.value, AdaptedCanonicalPathTests.clock, NNReal.coe_min, min_assoc, min_self]

/-- An ordinary continuous canonical martingale remains one under
almost every initial-state conditional law, in the same full past. -/
theorem conditional (Q : Measure (CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H)) [IsProbabilityMeasure Q]
    (M : ℝ≥0 → CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H → ℝ)
    (hM : Martingale M (filtration H) Q) (hM2 : ∀ t, MemLp (M t) 2 Q)
    (hc : ∀ x, Continuous (fun t ↦ M t x)) (hclip : ∀ t, M t = M (min t H)) :
    ∀ᵐ z ∂CanonicalInitialKernel.initialLaw H Q,
      Martingale M (filtration H) (CanonicalInitialKernel.kernel H Q z) ∧
        ∀ t, MemLp (M t) 2 (CanonicalInitialKernel.kernel H Q z) := by
  letI : MetricSpace (CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H) :=
    TopologicalSpace.metrizableSpaceMetric _
  exact ConditionalCountablePastTests.martingale Q (filtration H) M hM hM2 hc H hclip
    (state H 0) (state_adapted H 0) (CanonicalStateDriverFiltration.history H)
    (fun _ ↦ Measurable.of_comap_le le_rfl) (history H) (fun _ ↦ le_rfl)

/-- The energy-envelope version requires no second moment of the
martingale itself, so it also covers quadratic unbounded characteristics. -/
theorem conditional_integrable
    (Q : Measure (CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H)) [IsProbabilityMeasure Q]
    (M : ℝ≥0 → CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H → ℝ)
    (hM : Martingale M (filtration H) Q)
    (hc : ∀ x,Continuous (fun t => M t x))
    (D : CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H → ℝ)
    (hD : Integrable D Q) (hb : ∀ t x,‖M t x‖≤D x) :
    ∀ᵐ z ∂CanonicalInitialKernel.initialLaw H Q,
      Martingale M (filtration H) (CanonicalInitialKernel.kernel H Q z) :=
  ConditionalIntegrablePastTests.martingale Q (filtration H) M hM hc D hD hb
    (state H 0) (state_adapted H 0) (CanonicalStateDriverFiltration.history H)
    (fun _ => Measurable.of_comap_le le_rfl) (history H) (fun _ => le_rfl)

end SHEStochastic.CanonicalProcessTimeRegularity
