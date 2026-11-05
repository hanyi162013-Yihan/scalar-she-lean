module

public import SHE.PredictableL2

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.PredictableClock
open MeasureTheory Set
open scoped NNReal
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Every deterministic Borel time function is predictable. -/
theorem time_measurable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) :
    @Measurable (ℝ≥0 × Ω) ℝ≥0 𝓕.predictable _ Prod.fst := by
  apply measurable_of_Ioi
  intro t
  have hs := measurableSet_predictable_Ioi_prod (𝓕 := 𝓕) (i := t) MeasurableSet.univ
  convert hs using 1
  ext p
  simp only [mem_preimage,mem_Ioi,mem_prod,mem_univ,and_true]

theorem real_time_measurable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) :
    @Measurable (ℝ≥0 × Ω) ℝ 𝓕.predictable _ (fun p => (p.1:ℝ)) :=
  NNReal.continuous_coe.measurable.comp (time_measurable 𝓕)

end SHE.PredictableClock
