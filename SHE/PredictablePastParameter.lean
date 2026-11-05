module

public import SHE.PredictableClock

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.PredictablePastParameter
open Set MeasureTheory
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

def held (v : ℝ≥0) (u : Ω → E) (e : E) (p : ℝ≥0 × Ω) : E :=
  if v<p.1 then u p.2 else e

/-- A parameter known at v is predictably available strictly after v.
The value before v is fixed; the future random parameter is never
silently declared predictable on the whole original time axis. -/
theorem held_measurable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (v : ℝ≥0) (u : Ω → E) (hu : Measurable[𝓕 v] u) (e : E) :
    @Measurable (ℝ≥0 × Ω) E 𝓕.predictable _ (held v u e) := by
  intro s hs
  have hright : MeasurableSet[𝓕.predictable] (Ioi v ×ˢ (u ⁻¹' s)) :=
    measurableSet_predictable_Ioi_prod (hu hs)
  have htime : MeasurableSet[𝓕.predictable] (Ioi v ×ˢ (univ : Set Ω)) :=
    measurableSet_predictable_Ioi_prod MeasurableSet.univ
  by_cases he : e∈s
  · have hpre : held v u e ⁻¹' s = (Ioi v ×ˢ (u ⁻¹' s)) ∪ (Ioi v ×ˢ (univ : Set Ω))ᶜ := by
      ext p
      by_cases hp : v<p.1 <;> simp [held,hp,he]
    rw [hpre]
    exact hright.union htime.compl
  · have hpre : held v u e ⁻¹' s = Ioi v ×ˢ (u ⁻¹' s) := by
      ext p
      by_cases hp : v<p.1 <;> simp [held,hp,he]
    rw [hpre]
    exact hright

theorem held_eq {v : ℝ≥0} (u : Ω → E) (e : E) {p : ℝ≥0 × Ω} (hp : v<p.1) :
    held v u e p=u p.2 := if_pos hp

end SHE.PredictablePastParameter
