module

public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.Sequences

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.TightLawSubsequence
open MeasureTheory Filter Set TopologicalSpace
open scoped Topology

variable {X : Type*} [TopologicalSpace X] [MetrizableSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

/-- The public Prokhorov theorem supplies an actual weakly converging
subsequence from the proved uniform tightness of approximation laws. -/
theorem exists_limit (P : ℕ → ProbabilityMeasure X)
    (htight : IsTightMeasureSet (range (fun k ↦ (P k : Measure X)))) :
    ∃ Q : ProbabilityMeasure X, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (P ∘ φ) atTop (𝓝 Q) := by
  have he : {((ν : ProbabilityMeasure X) : Measure X) | ν ∈ range P} =
      range (fun k ↦ (P k : Measure X)) := by
    ext ν
    constructor
    · rintro ⟨π, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨P k, ⟨k, rfl⟩, rfl⟩
  have hc : IsCompact (closure (range P)) :=
    isCompact_closure_of_isTightMeasureSet (by rwa [he])
  obtain ⟨Q, _, φ, hφ, hlim⟩ := hc.tendsto_subseq
    (fun k ↦ subset_closure (mem_range_self k))
  exact ⟨Q, φ, hφ, hlim⟩

end SHEStochastic.TightLawSubsequence
