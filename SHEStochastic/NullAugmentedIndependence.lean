module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.NullMeasurable

/-! Independence survives adjoining all ambient null events to a past
sigma algebra. This is the measure-theoretic step needed by the paper's
completed independent-product filtration. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NullAugmentedIndependence
open MeasureTheory ProbabilityTheory Set
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)

@[instance_reducible] def aeSigma (m : MeasurableSpace Ω) : MeasurableSpace Ω where
  MeasurableSet' s := ∃ t, MeasurableSet[m] t ∧ s =ᵐ[μ] t
  measurableSet_empty := ⟨∅, MeasurableSet.empty, Filter.EventuallyEqSet.rfl⟩
  measurableSet_compl := by
    rintro s ⟨t, ht, he⟩
    exact ⟨tᶜ, ht.compl, he.compl⟩
  measurableSet_iUnion := by
    intro f hf
    choose g hg he using hf
    refine ⟨⋃ n, g n, MeasurableSet.iUnion hg, ?_⟩
    filter_upwards [ae_all_iff.mpr he] with ω hω
    simp only [Set.mem_iUnion]
    exact propext (exists_congr (fun n ↦ iff_of_eq (hω n)))

theorem le_aeSigma (m : MeasurableSpace Ω) : m ≤ @aeSigma Ω mΩ μ m :=
  fun s hs ↦ ⟨s, hs, Filter.EventuallyEqSet.rfl⟩

theorem nullSigma_le (m : MeasurableSpace Ω) :
    MeasurableSpace.generateFrom {s : Set Ω | μ s = 0} ≤ @aeSigma Ω mΩ μ m := by
  apply MeasurableSpace.generateFrom_le
  intro s hs
  exact ⟨∅, MeasurableSet.empty, ae_eq_empty.mpr hs⟩

theorem indep_aeSigma {m₁ m₂ : MeasurableSpace Ω} (h : Indep m₁ m₂ μ) :
    Indep m₁ (@aeSigma Ω mΩ μ m₂) μ := by
  rw [Indep_iff] at h ⊢
  intro s t hs ht
  obtain ⟨u, hu, htu⟩ := ht
  rw [measure_congr (Filter.EventuallyEqSet.rfl.inter htu), measure_congr htu]
  exact h s u hs hu

theorem indep_sup_null {m₁ m₂ : MeasurableSpace Ω} (h : Indep m₁ m₂ μ) :
    Indep m₁ (m₂ ⊔ MeasurableSpace.generateFrom {s : Set Ω | μ s = 0}) μ :=
  indep_of_indep_of_le_right (@indep_aeSigma Ω mΩ μ m₁ m₂ h)
    (sup_le (@le_aeSigma Ω mΩ μ m₂) (@nullSigma_le Ω mΩ μ m₂))

end SHEStochastic.NullAugmentedIndependence
