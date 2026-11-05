module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Data.Finset.Max

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic.SequentialIndependence
open MeasureTheory ProbabilityTheory

variable {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [LinearOrder ι]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Independence of each variable from the sigma algebra containing all
earlier variables gives joint independence. The proof removes the last
index of each finite test family. -/
theorem iIndepFun (m : ι → MeasurableSpace Ω) (X : ι → Ω → E)
    (hpast : ∀ i j, j < i → Measurable[m i] (X j))
    (hstep : ∀ i, Indep (MeasurableSpace.comap (X i) inferInstance) (m i) μ) :
    ProbabilityTheory.iIndepFun X μ := by
  classical
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro S sets hsets
  induction S using Finset.induction_on_max with
  | empty => simp
  | @insert a S hlt ih =>
    have ha : a ∉ S := fun ha ↦ (lt_irrefl a) (hlt a ha)
    have hA : MeasurableSet[MeasurableSpace.comap (X a) inferInstance]
        (X a ⁻¹' sets a) := ⟨sets a, hsets a (Finset.mem_insert_self _ _), rfl⟩
    have hB : MeasurableSet[m a] (⋂ j ∈ S, X j ⁻¹' sets j) := by
      apply S.measurableSet_biInter
      intro j hj
      exact hpast a j (hlt j hj) (hsets j (Finset.mem_insert_of_mem hj))
    rw [Finset.set_biInter_insert, Finset.prod_insert ha,
      (Indep_iff _ _ _).mp (hstep a) _ _ hA hB,
      ih (fun j hj ↦ hsets j (Finset.mem_insert_of_mem hj))]

end SHEStochastic.SequentialIndependence
