module

public import SHEStochastic.HilbertSimpleInputs
public import SHEStochastic.NativeRowRepresentatives
public import Mathlib.Topology.Sequences

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.BoundedPredictableDensity
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal Topology

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}
local notation "νin" => FiniteScalarIto.inputMeasure F μ H

/-- Reuse the existing simple-row density in the original input space.
The original and native predictable measures are equal. -/
theorem dense (e : HilbertBasis ι ℝ C) :
    Dense {u : Process (E := C) F μ H | ∃ M : ℝ≥0, ∀ᵐ p ∂νin, ‖u p‖ ≤ M} := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  change Dense {u : Lp C 2 ((energyMeasure μ H).trim (predictable_le_product F)) |
    ∃ M : ℝ≥0, ∀ᵐ p ∂νin, ‖u p‖ ≤ M}
  rw [← NativeRowRepresentatives.inputMeasure_eq]
  apply (HilbertSimpleInputs.embedding_dense (F := F) (μ := μ) (H := H) e).mono
  rintro u ⟨V, rfl⟩
  obtain ⟨K, hK⟩ := V.val.coe_bounded
  refine ⟨⟨max K 0, le_max_right _ _⟩, ?_⟩
  filter_upwards [HilbertSimpleInputs.embedding_ae F μ H V] with p hp
  rw [hp]
  exact (hK p.1 p.2).trans (le_max_left _ _)

theorem exists_sequence (e : HilbertBasis ι ℝ C) (u : Process (E := C) F μ H) :
    ∃ v : ℕ → Process (E := C) F μ H,
      (∀ n, ∃ M : ℝ≥0, ∀ᵐ p ∂νin, ‖v n p‖ ≤ M) ∧
      Filter.Tendsto v Filter.atTop (𝓝 u) := by
  obtain ⟨v, hv, ht⟩ := mem_closure_iff_seq_limit.mp (dense e u)
  exact ⟨v, hv, ht⟩

end SHEStochastic.BoundedPredictableDensity
