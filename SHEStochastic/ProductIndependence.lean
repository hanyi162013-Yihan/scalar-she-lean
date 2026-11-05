module

public import SHEStochastic.NullAugmentedIndependence
public import Mathlib.MeasureTheory.Measure.Prod
public import SHE.IndependentNoiseCompletion

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.ProductIndependence
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
variable {Ω Ξ : Type*} [mΩ : MeasurableSpace Ω] [mΞ : MeasurableSpace Ξ]
  (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Independence in each factor combines to independence of the paired
future and paired past on the actual product probability space. -/
theorem independent_products {m₁ m₂ : MeasurableSpace Ω} {n₁ n₂ : MeasurableSpace Ξ}
    (hm₁ : m₁ ≤ mΩ) (hm₂ : m₂ ≤ mΩ) (hn₁ : n₁ ≤ mΞ) (hn₂ : n₂ ≤ mΞ)
    (hμ : Indep m₁ m₂ μ) (hν : Indep n₁ n₂ ν) :
    Indep (m₁.prod n₁) (m₂.prod n₂) (@Measure.prod Ω Ξ mΩ mΞ μ ν) := by
  refine IndepSets.indep
    (sup_le_sup (MeasurableSpace.comap_mono hm₁) (MeasurableSpace.comap_mono hn₁))
    (sup_le_sup (MeasurableSpace.comap_mono hm₂) (MeasurableSpace.comap_mono hn₂))
    (@isPiSystem_prod Ω Ξ m₁ n₁) (@isPiSystem_prod Ω Ξ m₂ n₂)
    (@generateFrom_prod Ω Ξ m₁ n₁).symm (@generateFrom_prod Ω Ξ m₂ n₂).symm ?_
  rw [IndepSets_iff]
  rintro s t ⟨s₁, hs₁, t₁, ht₁, rfl⟩ ⟨s₂, hs₂, t₂, ht₂, rfl⟩
  simp only [Set.prod_inter_prod, Measure.prod_prod]
  rw [(Indep_iff _ _ μ).mp hμ s₁ s₂ hs₁ hs₂,
    (Indep_iff _ _ ν).mp hν t₁ t₂ ht₁ ht₂]
  ac_rfl

/-- The same paired future is independent of the completed product past,
which includes every null event of the ambient joint probability. -/
theorem independent_completed_past
    (F : Filtration ℝ≥0 mΩ) (G : Filtration ℝ≥0 mΞ) (s : ℝ≥0)
    {m₁ : MeasurableSpace Ω} {n₁ : MeasurableSpace Ξ}
    (hm₁ : m₁ ≤ mΩ) (hn₁ : n₁ ≤ mΞ)
    (hμ : Indep m₁ (F s) μ) (hν : Indep n₁ (G s) ν) :
    Indep (m₁.prod n₁) (@SHE.IndependentNoiseCompletion.filtration Ω Ξ mΩ mΞ μ ν F G s)
      (@SHE.IndependentNoiseCompletion.measure Ω Ξ mΩ mΞ μ ν) := by
  have h := @NullAugmentedIndependence.indep_sup_null (Ω × Ξ)
    (mΩ.prod mΞ) (@Measure.prod Ω Ξ mΩ mΞ μ ν) (m₁.prod n₁) ((F s).prod (G s))
    (@independent_products Ω Ξ mΩ mΞ μ ν _ _ _ _ _ _ hm₁ (F.le s) hn₁ (G.le s) hμ hν)
  exact h

end SHEStochastic.ProductIndependence
