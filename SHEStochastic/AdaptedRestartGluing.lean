module

public import SHE.DeterministicItoShiftClock
public import SHE.NullCompleteFiltration

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.AdaptedRestartGluing
open MeasureTheory SHE
open scoped NNReal

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Glue a stopped prefix and a stopped future, anchoring the latter at
its time-zero value. This gives continuous paths for every sample even
when the matching initial condition is only almost sure. -/
def value (v h : ℝ≥0) (U V : ℝ≥0 → Ω → E) (t : ℝ≥0) (ω : Ω) : E :=
  U (min t v) ω + (V (min (t-v) h) ω - V 0 ω)

theorem before (v h : ℝ≥0) (U V : ℝ≥0 → Ω → E) (t : ℝ≥0) (ht : t ≤ v) :
    value v h U V t = U t := by
  funext ω
  simp only [value, min_eq_left ht, tsub_eq_zero_of_le ht, min_eq_left (show (0 : ℝ≥0) ≤ h from zero_le), sub_self, add_zero]

theorem after (v h : ℝ≥0) (U V : ℝ≥0 → Ω → E) (t : ℝ≥0) (ht : v ≤ t) :
    value v h U V t = fun ω ↦ U v ω + (V (min (t-v) h) ω - V 0 ω) := by
  funext ω
  simp only [value, min_eq_right ht]

theorem continuous (v h : ℝ≥0) (U V : ℝ≥0 → Ω → E)
    (hU : ∀ ω, Continuous (U · ω)) (hV : ∀ ω, Continuous (V · ω)) :
    ∀ ω, Continuous (value v h U V · ω) := by
  intro ω
  exact ((hU ω).comp (continuous_id.min continuous_const)).add
    (((hV ω).comp ((continuous_id.sub continuous_const).min continuous_const)).sub continuous_const)

theorem adapted (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (v h : ℝ≥0)
    (U V : ℝ≥0 → Ω → E) (hU : StronglyAdapted F U)
    (hV : StronglyAdapted (SHE.DeterministicItoShift.filtration F v) V) :
    StronglyAdapted F (value v h U V) := by
  intro t
  by_cases ht : t ≤ v
  · rw [before v h U V t ht]
    exact hU t
  · have hvt : v ≤ t := (lt_of_not_ge ht).le
    rw [after v h U V t hvt]
    have hs : v + min (t-v) h ≤ t := by
      calc
        _ ≤ v + (t-v) := add_le_add le_rfl (min_le_left _ _)
        _ = t := add_tsub_cancel_of_le hvt
    have h0 := hV 0
    change StronglyMeasurable[F (v+0)] (V 0) at h0
    rw [add_zero] at h0
    exact ((hU v).mono (F.mono hvt)).add
      (((hV (min (t-v) h)).mono (F.mono hs)).sub (h0.mono (F.mono hvt)))

theorem predictable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (v h : ℝ≥0)
    (U V : ℝ≥0 → Ω → E) (hU : StronglyAdapted F U)
    (hV : StronglyAdapted (SHE.DeterministicItoShift.filtration F v) V)
    (hcU : ∀ ω, Continuous (U · ω)) (hcV : ∀ ω, Continuous (V · ω)) :
    StronglyMeasurable[F.predictable] (Function.uncurry (value v h U V)) :=
  ContinuousPredictable.stronglyMeasurable F _ (adapted F v h U V hU hV)
    (continuous v h U V hcU hcV)

theorem future_ae (μ : Measure Ω) (v h : ℝ≥0) (U V : ℝ≥0 → Ω → E)
    (hInitial : V 0 =ᵐ[μ] U v) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, v ≤ t → value v h U V t ω = V (min (t-v) h) ω := by
  filter_upwards [hInitial] with ω hi t ht
  rw [after v h U V t ht]
  change U v ω + (V (min (t-v) h) ω - V 0 ω) = _
  rw [hi]
  abel

end SHEStochastic.AdaptedRestartGluing
