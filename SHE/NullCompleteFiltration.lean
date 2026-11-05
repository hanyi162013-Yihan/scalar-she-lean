module

public import SHE.ContinuousPredictable

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace SHE.NullCompleteFiltration
open MeasureTheory Set
open scoped NNReal

variable {Ω E : Type*} [MeasurableSpace Ω]

/-- The usual null-set part of completeness: every set of ambient outer
measure zero belongs to every time sigma algebra. This is a condition on
the filtration, not a theorem about the stochastic convolution. -/
def ContainsNullSets (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) : Prop :=
  ∀ (t : ℝ≥0) (A : Set Ω), μ A=0 → MeasurableSet[𝓕 t] A

variable [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω)

theorem stronglyMeasurable_congr (hnull : ContainsNullSets 𝓕 μ) (t : ℝ≥0)
    {f g : Ω → E} (hg : StronglyMeasurable[𝓕 t] g) (hfg : f =ᵐ[μ] g) :
    StronglyMeasurable[𝓕 t] f := by
  classical
  let bad : Set Ω := {ω | f ω ≠ g ω}
  have hbad : μ bad=0 := by
    exact ae_iff.mp hfg
  have hmbad : MeasurableSet[𝓕 t] bad := hnull t bad hbad
  apply stronglyMeasurable_iff_measurable.mpr
  intro B hB
  have he : f ⁻¹' B=(g ⁻¹' B \ bad) ∪ (f ⁻¹' B ∩ bad) := by
    ext ω
    by_cases hω : f ω=g ω <;> simp [bad,hω]
  rw [he]
  apply MeasurableSet.union ((hg.measurable hB).diff hmbad)
  exact hnull t _ (measure_mono_null inter_subset_right hbad)

/-- Fixed-time almost-everywhere modifications inherit adaptation in a
null-complete filtration, even when the original family was given only
through adapted representatives. -/
theorem stronglyAdapted_of_versions (hnull : ContainsNullSets 𝓕 μ)
    (u : ℝ≥0 → Ω → E)
    (hu : ∀ t, ∃ Z : Ω → E, StronglyMeasurable[𝓕 t] Z ∧ u t =ᵐ[μ] Z) :
    StronglyAdapted 𝓕 u := by
  intro t
  obtain ⟨Z,hZ,hEq⟩ := hu t
  exact stronglyMeasurable_congr 𝓕 μ hnull t hZ hEq

theorem predictable_of_continuous_versions (hnull : ContainsNullSets 𝓕 μ)
    (u : ℝ≥0 → Ω → E)
    (hu : ∀ t, ∃ Z : Ω → E, StronglyMeasurable[𝓕 t] Z ∧ u t =ᵐ[μ] Z)
    (hc : ∀ ω, Continuous (fun t => u t ω)) :
    StronglyMeasurable[𝓕.predictable] (Function.uncurry u) :=
  ContinuousPredictable.stronglyMeasurable 𝓕 u (stronglyAdapted_of_versions 𝓕 μ hnull u hu) hc

end SHE.NullCompleteFiltration
