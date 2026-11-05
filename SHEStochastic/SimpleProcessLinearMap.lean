module

public import SHEStochastic.FilteredSimplePartition

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.SimpleProcessLinearMap
open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω E G : Type*} {mΩ : MeasurableSpace Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G]
  {F : Filtration ℝ≥0 mΩ}

/-- Applying a continuous linear map preserves bounded predictable
simple processes without introducing any additional time intervals. -/
def map (L : E →L[ℝ] G) (V : SimpleProcess E F) : SimpleProcess G F := by
  classical
  let f : (Ω → E) → (Ω → G) := fun v ω ↦ L (v ω)
  have hf : f 0 = 0 := by funext ω; exact L.map_zero
  refine { valueBot := fun ω ↦ L (V.valueBot ω)
           value := V.value.mapRange f hf
           le_of_mem_support_value := ?_
           measurable_valueBot := L.measurable.comp V.measurable_valueBot
           measurable_value' := ?_
           bounded_valueBot := ?_
           bounded_value := ?_ }
  · intro p hp
    exact V.le_of_mem_support_value p (Finsupp.support_mapRange (hf := hf) hp)
  · intro p hp
    exact L.measurable.comp (V.measurable_value p)
  · exact ⟨‖L‖ * V.valueBotBound, fun ω ↦
      (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (V.valueBot_le_valueBotBound ω) L.opNorm_nonneg)⟩
  · exact ⟨‖L‖ * V.valueBound, fun p _ ω ↦
      (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (V.value_le_valueBound p ω) L.opNorm_nonneg)⟩

@[simp] theorem value_map (L : E →L[ℝ] G) (V : SimpleProcess E F) (p : ℝ≥0 × ℝ≥0) (ω : Ω) :
    (map L V).value p ω = L (V.value p ω) := rfl

@[simp] theorem valueBot_map (L : E →L[ℝ] G) (V : SimpleProcess E F) (ω : Ω) :
    (map L V).valueBot ω = L (V.valueBot ω) := rfl

theorem support_map (L : E →L[ℝ] G) (V : SimpleProcess E F) :
    (map L V).value.support ⊆ V.value.support := by
  exact Finsupp.support_mapRange (hf := funext fun _ ↦ L.map_zero)

@[simp] theorem apply_map (L : E →L[ℝ] G) (V : SimpleProcess E F) (t : ℝ≥0) (ω : Ω) :
    (map L V) t ω = L (V t ω) := by
  rw [SimpleProcess.apply_eq, SimpleProcess.apply_eq, map_add]
  congr 1
  · by_cases ht : t = 0 <;> simp [map, Pi.single_apply, ht]
  · change (V.value.mapRange (fun f ω ↦ L (f ω)) (funext fun _ ↦ L.map_zero)).sum
      (fun p f ↦ (Set.Ioc p.1 p.2).indicator (fun _ ↦ f ω) t) =
      L (V.value.sum (fun p f ↦ (Set.Ioc p.1 p.2).indicator (fun _ ↦ f ω) t))
    rw [Finsupp.sum_mapRange_index (by intro p; simp)]
    simp only [Finsupp.sum, map_sum]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases ht : t ∈ Set.Ioc p.1 p.2 <;> simp [ht]

end SHEStochastic.SimpleProcessLinearMap
