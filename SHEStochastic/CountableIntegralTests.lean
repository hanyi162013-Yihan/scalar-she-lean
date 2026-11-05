module

public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.PiSystem

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.CountableIntegralTests
open MeasureTheory Set

variable (X : Type*) [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X]

/-- A countable algebra of finite intersections, including the whole
space, sufficient for every finite signed integral test. -/
def testSet (s : Finset ℕ) : Set X := ⋂ n ∈ s, MeasurableSpace.natGeneratingSequence X n

theorem measurable_testSet (s : Finset ℕ) : MeasurableSet (testSet X s) := by
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iInter
  intro _
  exact MeasurableSpace.measurableSet_natGeneratingSequence n

theorem testSet_union (s t : Finset ℕ) : testSet X (s ∪ t) = testSet X s ∩ testSet X t := by
  ext x
  simp only [testSet, mem_iInter, Finset.mem_union, mem_inter_iff, or_imp, forall_and]

theorem piSystem : IsPiSystem (Set.range (testSet X)) := by
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ _
  exact ⟨s ∪ t, testSet_union X s t⟩

theorem generates : (inferInstance : MeasurableSpace X) = MeasurableSpace.generateFrom (Set.range (testSet X)) := by
  apply le_antisymm
  · calc
      _ = MeasurableSpace.generateFrom (Set.range (MeasurableSpace.natGeneratingSequence X)) :=
        (MeasurableSpace.generateFrom_natGeneratingSequence X).symm
      _ ≤ _ := MeasurableSpace.generateFrom_mono (by
        rintro _ ⟨n, rfl⟩
        exact ⟨{n}, by simp [testSet]⟩)
  · apply MeasurableSpace.generateFrom_le
    rintro _ ⟨s, rfl⟩
    exact measurable_testSet X s

/-- Countably many generator set integrals determine all measurable
past tests, with no choice of a dense family depending on the measure. -/
theorem extend {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Ω → X) (hY : Measurable Y) (f : Ω → ℝ) (hf : Integrable f μ)
    (hbasic : ∀ s : Finset ℕ, (∫ sample in Y ⁻¹' testSet X s, f sample ∂μ) = 0) :
    ∀ A : Set X, MeasurableSet A → (∫ sample in Y ⁻¹' A, f sample ∂μ) = 0 := by
  have htotal : (∫ sample, f sample ∂μ) = 0 := by simpa [testSet] using hbasic ∅
  refine MeasurableSpace.induction_on_inter
    (C := fun A _ ↦ (∫ sample in Y ⁻¹' A, f sample ∂μ) = 0) (generates X) (piSystem X) ?_ ?_ ?_ ?_
  · simp
  · rintro _ ⟨s, rfl⟩
    exact hbasic s
  · intro A hA hzero
    rw [preimage_compl, setIntegral_compl (hY hA) hf, htotal, hzero, sub_self]
  · intro A hd hm hz
    rw [preimage_iUnion, integral_iUnion (fun n ↦ hY (hm n))
      (fun i j hij ↦ (hd hij).preimage Y) hf.integrableOn]
    simp only [hz, tsum_zero]

end SHEStochastic.CountableIntegralTests
