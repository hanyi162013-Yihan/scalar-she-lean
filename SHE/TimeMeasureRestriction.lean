module

public import SHE.TimeMeasureMass

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.PredictableL2
open MeasureTheory Set
open scoped NNReal

theorem timeMeasure_restrict {h t : ℝ≥0} (ht : t ≤ h) :
    (timeMeasure h).restrict (Ioc 0 t)=timeMeasure t := by
  have hp : ((↑) : ℝ≥0 → ℝ) ⁻¹' Ioc (0:ℝ) (t:ℝ)=Ioc 0 t := by
    ext r
    simp only [mem_preimage,mem_Ioc,NNReal.coe_pos,NNReal.coe_le_coe]
  change (((volume : Measure ℝ).restrict (Ioc (0:ℝ) (h:ℝ))).comap ((↑) : ℝ≥0 → ℝ)).restrict
    (Ioc 0 t)=_
  rw [← hp,← nonnegative_coe_measurableEmbedding.comap_restrict,Measure.restrict_restrict measurableSet_Ioc]
  rw [inter_eq_left.mpr (Ioc_subset_Ioc_right (show (t:ℝ) ≤ (h:ℝ) by exact_mod_cast ht))]
  rfl

end SHE.PredictableL2
