module

public import SHE.DeterministicItoShiftMeasure
public import SHE.TimeMeasureRestriction

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.FiniteBlockEnergyMeasure
open MeasureTheory Set SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The product clock on the next unit horizon is the preceding clock
plus its last unit interval. -/
theorem succ (k : ℕ) :
    energyMeasure μ ((k + 1 : ℕ) : ℝ≥0) =
      energyMeasure μ (k : ℝ≥0) +
        (energyMeasure μ ((k + 1 : ℕ) : ℝ≥0)).restrict
          (Ioc (k : ℝ≥0) ((k + 1 : ℕ) : ℝ≥0) ×ˢ univ) := by
  let A : Set (ℝ≥0 × Ω) := Ioc 0 (k : ℝ≥0) ×ˢ univ
  let B : Set (ℝ≥0 × Ω) := Ioc (k : ℝ≥0) ((k+1 : ℕ) : ℝ≥0) ×ˢ univ
  have hAB : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro p hpA hpB
    exact (not_lt_of_ge hpA.1.2) hpB.1.1
  have hmB : MeasurableSet B := measurableSet_Ioc.prod MeasurableSet.univ
  have hsupport : ∀ᵐ p ∂energyMeasure μ ((k+1 : ℕ) : ℝ≥0), p ∈ A ∪ B := by
    have hm : MeasurableSet (A ∪ B) :=
      (measurableSet_Ioc.prod MeasurableSet.univ).union hmB
    apply (Measure.ae_prod_iff_ae_ae hm).mpr
    filter_upwards [timeMeasure_ae_mem ((k+1 : ℕ) : ℝ≥0)] with t ht
    filter_upwards [] with ω
    by_cases htk : t ≤ (k : ℝ≥0)
    · exact Or.inl ⟨⟨ht.1,htk⟩,mem_univ _⟩
    · exact Or.inr ⟨⟨lt_of_not_ge htk,ht.2⟩,mem_univ _⟩
  have hA : (energyMeasure μ ((k+1 : ℕ) : ℝ≥0)).restrict A =
      energyMeasure μ (k : ℝ≥0) := by
    dsimp only [A,energyMeasure]
    rw [← Measure.prod_restrict,Measure.restrict_univ,
      timeMeasure_restrict (show (k : ℝ≥0) ≤ ((k+1 : ℕ) : ℝ≥0) by norm_cast; omega)]
  calc
    energyMeasure μ ((k+1 : ℕ) : ℝ≥0) =
        (energyMeasure μ ((k+1 : ℕ) : ℝ≥0)).restrict (A ∪ B) :=
      (Measure.restrict_eq_self_of_ae_mem hsupport).symm
    _ = (energyMeasure μ ((k+1 : ℕ) : ℝ≥0)).restrict A +
        (energyMeasure μ ((k+1 : ℕ) : ℝ≥0)).restrict B :=
      Measure.restrict_union hAB hmB
    _ = _ := by rw [hA]

end SHEStochastic.FiniteBlockEnergyMeasure
