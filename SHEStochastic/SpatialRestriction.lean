module

public import SHEStochastic.BoundedFieldOperator
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.SpatialRestriction
open MeasureTheory
open scoped NNReal
variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A single bounded indicator multiplier, shared by the profile and
output Hilbert spaces. -/
def field (s : Set X) (hs : MeasurableSet s) : BoundedFieldOperator.Field μ E E where
  value := s.indicator (fun _ => ContinuousLinearMap.id ℝ E)
  measurable := aestronglyMeasurable_const.indicator hs
  bound := 1
  norm_bound := by
    filter_upwards with x
    by_cases hx : x∈s
    · simpa only [Set.indicator_of_mem hx, NNReal.coe_one] using
        (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E))
    · simp only [Set.indicator_of_notMem hx, norm_zero, NNReal.coe_one, zero_le_one]

def operator (s : Set X) (hs : MeasurableSet s) : Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  BoundedFieldOperator.operator (field s hs)

theorem operator_ae (s : Set X) (hs : MeasurableSet s) (u : Lp E 2 μ) :
    ⇑(operator s hs u) =ᵐ[μ] s.indicator u := by
  filter_upwards [BoundedFieldOperator.operator_ae (field s hs) u] with x hx
  change BoundedFieldOperator.operator (field s hs) u x=_
  rw [hx]
  by_cases hxs : x∈s <;> simp [field, hxs]

theorem integral (s : Set X) (hs : MeasurableSet s) (u : Lp E 2 μ) :
    (∫ x, operator s hs u x ∂μ)=∫ x in s, u x ∂μ := by
  rw [integral_congr_ae (operator_ae s hs u), integral_indicator hs]

end SHEStochastic.SpatialRestriction
