module

public import SHE.IntervalTimeMeasure

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace SHE.PredictableL2
open MeasureTheory Set
open scoped NNReal ENNReal

theorem causal_lintegral_of_zero {h t : ℝ≥0} (ht : t ≤ h)
    (F : ℝ≥0 → ℝ≥0∞) (hF : ∀ r,t < r → F r=0) :
    (∫⁻ r,F r ∂timeMeasure h)=∫⁻ r,F r ∂timeMeasure t := by
  rw [← timeMeasure_restrict ht,← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr_ae
  filter_upwards [timeMeasure_ae_mem h] with r hr
  by_cases hrt : r ≤ t
  · rw [Set.indicator_of_mem (show r ∈ Ioc 0 t from ⟨hr.1,hrt⟩)]
  · rw [Set.indicator_of_notMem (show r ∉ Ioc 0 t from fun hs => hrt hs.2),hF r (lt_of_not_ge hrt)]

theorem timeMeasure_split {s t : ℝ≥0} (hst : s ≤ t) :
    timeMeasure t=timeMeasure s+intervalTimeMeasure s t := by
  have he : Ioc (0:ℝ≥0) t=Ioc 0 s ∪ Ioc s t := by
    ext r
    constructor
    · intro hr
      by_cases hrs : r ≤ s
      · exact Or.inl ⟨hr.1,hrs⟩
      · exact Or.inr ⟨lt_of_not_ge hrs,hr.2⟩
    · rintro (hr | hr)
      · exact ⟨hr.1,hr.2.trans hst⟩
      · exact ⟨s.2.trans_lt hr.1,hr.2⟩
  have hd : Disjoint (Ioc (0:ℝ≥0) s) (Ioc s t) := by
    apply Set.disjoint_left.mpr
    intro r hr hr'
    exact (not_lt_of_ge hr.2) hr'.1
  calc
    _ = (timeMeasure t).restrict (Ioc 0 t) :=
      (Measure.restrict_eq_self_of_ae_mem (timeMeasure_ae_mem t)).symm
    _ = (timeMeasure t).restrict (Ioc 0 s)+(timeMeasure t).restrict (Ioc s t) := by
      rw [he,Measure.restrict_union hd measurableSet_Ioc]
    _ = _ := by rw [timeMeasure_restrict hst,timeMeasure_restrict_Ioc s le_rfl]

end SHE.PredictableL2
