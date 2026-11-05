module

public import SHEStochastic.HilbertSimplePartition

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic.NativeClockIntegral
open MeasureTheory
open scoped NNReal ENNReal

theorem before (H t : ℝ≥0) (htH : t ≤ H) (f : ℝ≥0 → ℝ) :
    (∫ r, (Set.Iio t).indicator f r ∂MathFin.ItoIntegralCLM.timeMeasure_T H) =
      ∫ r, f r ∂MathFin.ItoIntegralCLM.timeMeasure_T t := by
  let νt := MathFin.ItoIntegralCLM.timeMeasure_T H
  letI : NullSingletonClass MathFin.ItoIntegralL2.timeMeasure :=
    ⟨MathFin.ItoIntegralL2.timeMeasure_singleton⟩
  haveI : NullSingletonClass νt := by dsimp [νt, MathFin.ItoIntegralCLM.timeMeasure_T]; infer_instance
  have he : (Set.Iio t).indicator f =ᵐ[νt] (Set.Ioc 0 t).indicator f := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioc (a := 0) (b := H)), νt.ae_ne t]
      with r hr hne
    have hiff : r ∈ Set.Iio t ↔ r ∈ Set.Ioc 0 t := by
      simp only [Set.mem_Iio, Set.mem_Ioc]
      exact ⟨fun h ↦ ⟨hr.1, h.le⟩, fun h ↦ lt_of_le_of_ne h.2 hne⟩
    simp only [Set.indicator_apply, hiff]
  rw [integral_congr_ae he, integral_indicator measurableSet_Ioc]
  change (∫ r, f r ∂(MathFin.ItoIntegralL2.timeMeasure.restrict (Set.Ioc 0 H)).restrict (Set.Ioc 0 t)) =
    ∫ r, f r ∂MathFin.ItoIntegralL2.timeMeasure.restrict (Set.Ioc 0 t)
  rw [Measure.restrict_restrict measurableSet_Ioc,
    Set.inter_eq_left.mpr (Set.Ioc_subset_Ioc le_rfl htH)]

/-- Strict-before stopping and the closed right endpoint of a simple
time cell have the same integral: deterministic endpoints have zero mass. -/
theorem before_const (H t : ℝ≥0) (htH : t ≤ H) (c : ℝ) :
    (∫ r, (Set.Iio t).indicator (fun _ ↦ c) r ∂MathFin.ItoIntegralCLM.timeMeasure_T H) =
      (t : ℝ) * c := by
  let νt := MathFin.ItoIntegralCLM.timeMeasure_T H
  letI : NullSingletonClass MathFin.ItoIntegralL2.timeMeasure := ⟨MathFin.ItoIntegralL2.timeMeasure_singleton⟩
  haveI : NullSingletonClass νt := by dsimp [νt, MathFin.ItoIntegralCLM.timeMeasure_T]; infer_instance
  have hs : ∀ᵐ r ∂νt, r ∈ Set.Ioc 0 H := ae_restrict_mem measurableSet_Ioc
  have he : (Set.Iio t).indicator (fun _ ↦ c) =ᵐ[νt]
      (Set.Ioc 0 t).indicator (fun _ ↦ c) := by
    filter_upwards [hs, νt.ae_ne t] with r hr hne
    have hiff : r ∈ Set.Iio t ↔ r ∈ Set.Ioc 0 t := by
      simp only [Set.mem_Iio, Set.mem_Ioc]
      exact ⟨fun h ↦ ⟨hr.1, h.le⟩, fun h ↦ lt_of_le_of_ne h.2 hne⟩
    simp only [Set.indicator_apply, hiff]
  rw [integral_congr_ae he]
  simpa only [NNReal.coe_zero, sub_zero] using
    HilbertSimplePartition.integral_cell_const (H := H) 0 t zero_le htH c

end SHEStochastic.NativeClockIntegral
