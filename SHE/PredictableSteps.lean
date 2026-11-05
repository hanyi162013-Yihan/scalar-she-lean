module

public import SHE.PredictableL2
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace SHE.PredictableSteps
open MeasureTheory Set PredictableL2
open scoped ENNReal NNReal

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)

/-- A genuine predictable time cell: its random value is known at the
left endpoint, and it is used only strictly afterwards. -/
def step (l r : ℝ≥0) (Z : Ω → E) (p : ℝ≥0 × Ω) : E :=
  if p.1 ∈ Ioc l r then Z p.2 else 0

theorem step_stronglyMeasurable (l r : ℝ≥0) {Z : Ω → E}
    (hZ : StronglyMeasurable[𝓕 l] Z) :
    StronglyMeasurable[𝓕.predictable] (step l r Z) := by
  apply stronglyMeasurable_iff_measurable.mpr
  intro B hB
  have hcell : MeasurableSet[𝓕.predictable] (Ioc l r ×ˢ (univ : Set Ω)) :=
    measurableSet_predictable_Ioc_prod l r MeasurableSet.univ
  have hhit : MeasurableSet[𝓕.predictable] (Ioc l r ×ˢ (Z ⁻¹' B)) :=
    measurableSet_predictable_Ioc_prod l r (hZ.measurable hB)
  by_cases hz : (0 : E) ∈ B
  · have he : step l r Z ⁻¹' B=(Ioc l r ×ˢ (Z ⁻¹' B)) ∪ (Ioc l r ×ˢ (univ : Set Ω))ᶜ := by
      ext p
      by_cases hp : p.1 ∈ Ioc l r <;> simp [step,hp,hz]
    rw [he]
    exact hhit.union hcell.compl
  · have he : step l r Z ⁻¹' B=Ioc l r ×ˢ (Z ⁻¹' B) := by
      ext p
      by_cases hp : p.1 ∈ Ioc l r <;> simp [step,hp,hz]
    rw [he]
    exact hhit

omit [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem step_norm_le (l r : ℝ≥0) (Z : Ω → E) (p : ℝ≥0 × Ω) :
    ‖step l r Z p‖ ≤ ‖Z p.2‖ := by
  unfold step
  split_ifs <;> simp

theorem step_memLp (μ : Measure Ω) [SFinite μ] (h l r : ℝ≥0) {Z : Ω → E}
    (hZ : StronglyMeasurable[𝓕 l] Z) (hZ2 : MemLp Z 2 μ) :
    @MemLp _ _ 𝓕.predictable _ _ (step l r Z) 2
      ((energyMeasure μ h).trim (predictable_le_product 𝓕)) := by
  have hs := step_stronglyMeasurable 𝓕 l r hZ
  have hamb : MemLp (step l r Z) 2 (energyMeasure μ h) :=
    (hZ2.comp_snd (timeMeasure h)).mono
      (hs.mono (predictable_le_product 𝓕)).aestronglyMeasurable
      (Filter.Eventually.of_forall (step_norm_le l r Z))
  change eLpNorm (step l r Z) 2 ((energyMeasure μ h).trim (predictable_le_product 𝓕)) < ∞
  rw [eLpNorm_trim (predictable_le_product 𝓕) hs]
  exact hamb

/-- The actual complete predictable L² element represented by a cell. -/
def process (μ : Measure Ω) [SFinite μ] (h l r : ℝ≥0) (Z : Ω → E)
    (hZ : StronglyMeasurable[𝓕 l] Z) (hZ2 : MemLp Z 2 μ) :
    Process (E := E) 𝓕 μ h :=
  (step_memLp 𝓕 μ h l r hZ hZ2).toLp (step l r Z)

theorem process_ae (μ : Measure Ω) [SFinite μ] (h l r : ℝ≥0) (Z : Ω → E)
    (hZ : StronglyMeasurable[𝓕 l] Z) (hZ2 : MemLp Z 2 μ) :
    process 𝓕 μ h l r Z hZ hZ2 =ᵐ[energyMeasure μ h] step l r Z :=
  ae_eq_of_ae_eq_trim (step_memLp 𝓕 μ h l r hZ hZ2).coeFn_toLp

end SHE.PredictableSteps
