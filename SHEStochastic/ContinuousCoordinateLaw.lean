module

public import SHE.FiniteCoordinateLaw
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.ContinuousCoordinateLaw
open MeasureTheory

variable {Ω Ω' T ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [TopologicalSpace T] [SecondCountableTopology T] [LocallyCompactSpace T]

/-- Finite coordinate laws determine the law of a countable or
uncountable family of continuous real paths. The proof uses the existing
finite-dimensional law theorem and the evaluation-generated Borel sigma
algebra, without requiring a measurable set of continuous raw paths. -/
theorem map_eq (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (X : Ω → ι → C(T, ℝ)) (Y : Ω' → ι → C(T, ℝ)) (hX : Measurable X) (hY : Measurable Y)
    (hf : ∀ (n : ℕ) (a : Fin n → ι × T),
      μ.map (fun sample ↦ fun i ↦ X sample (a i).1 (a i).2) =
        ν.map (fun sample ↦ fun i ↦ Y sample (a i).1 (a i).2)) :
    μ.map X = ν.map Y := by
  let eval : (ι → C(T, ℝ)) → (ι × T → ℝ) := fun z p ↦ z p.1 p.2
  have hm : Measurable eval := measurable_pi_iff.mpr fun p ↦
    (ContinuousMap.measurable_eval p.2).comp (measurable_pi_apply p.1)
  have he : MeasurableSpace.comap eval inferInstance = (inferInstance : MeasurableSpace (ι → C(T, ℝ))) := by
    apply le_antisymm hm.comap_le
    have hi : @Measurable (ι → C(T, ℝ)) (ι → C(T, ℝ))
        (MeasurableSpace.comap eval inferInstance) inferInstance id := by
      letI : MeasurableSpace (ι → C(T, ℝ)) := MeasurableSpace.comap eval inferInstance
      apply measurable_pi_iff.mpr
      intro i
      apply ContinuousMap.measurable_iff_eval.mpr
      intro t
      exact (measurable_pi_apply (i,t)).comp (Measurable.of_comap_le le_rfl : Measurable eval)
    simpa only [MeasurableSpace.comap_id] using hi.comap_le
  have hall := SHE.FiniteCoordinateLaw.map_eq μ ν
    (fun p sample ↦ X sample p.1 p.2) (fun p sample ↦ Y sample p.1 p.2)
    (fun p ↦ (measurable_pi_apply p).comp (hm.comp hX))
    (fun p ↦ (measurable_pi_apply p).comp (hm.comp hY)) hf
  have hmaps : (μ.map X).map eval = (ν.map Y).map eval := by
    rw [Measure.map_map hm hX, Measure.map_map hm hY]
    exact hall
  ext A hA
  have hA' : MeasurableSet[MeasurableSpace.comap eval inferInstance] A := he.symm.le A hA
  obtain ⟨B, hB, rfl⟩ := hA'
  simpa only [Measure.map_apply hm hB] using congrArg (fun m : Measure (ι × T → ℝ) ↦ m B) hmaps

end SHEStochastic.ContinuousCoordinateLaw
