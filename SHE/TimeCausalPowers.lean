module

public import SHE.TimeMeasureRestriction
public import SHE.PredictableTime
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.PredictableL2
open MeasureTheory Set
open scoped NNReal ENNReal

/-- Exact physical causal power mass on the nonnegative time measure,
including the singular but integrable endpoint. -/
theorem causal_rpow_mass {α : ℝ} (hα : -1 < α) (t : ℝ≥0) :
    (∫⁻ s,ENNReal.ofReal (((t:ℝ)-(s:ℝ))^α) ∂timeMeasure t)=
      ENNReal.ofReal ((t:ℝ)^(α+1)/(α+1)) := by
  rw [timeMeasure_lintegral]
  have he : (∫⁻ r in Ioc (0:ℝ) (t:ℝ),ENNReal.ofReal (((t:ℝ)-(r.toNNReal:ℝ))^α))=
      ∫⁻ r in Ioc (0:ℝ) (t:ℝ),ENNReal.ofReal (((t:ℝ)-r)^α) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [Real.coe_toNNReal _ hr.1.le]
  rw [he]
  have hi : IntervalIntegrable (fun r : ℝ => r^α) volume 0 (t:ℝ) :=
    intervalIntegral.intervalIntegrable_rpow' hα
  have ht : IntervalIntegrable (fun r : ℝ => ((t:ℝ)-r)^α) volume 0 (t:ℝ) := by
    simpa only [sub_zero,sub_self] using (hi.comp_sub_left (t:ℝ)).symm
  have hp : 0 ≤ᵐ[volume.restrict (Ioc (0:ℝ) (t:ℝ))] (fun r : ℝ => ((t:ℝ)-r)^α) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact Real.rpow_nonneg (sub_nonneg.mpr hr.2) α
  have ho := ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le t.2).mp ht) hp
  change ENNReal.ofReal (∫ r in Ioc (0:ℝ) (t:ℝ),((t:ℝ)-r)^α ∂volume)=
    ∫⁻ r in Ioc (0:ℝ) (t:ℝ),ENNReal.ofReal (((t:ℝ)-r)^α) ∂volume at ho
  have hioc : (∫ r in Ioc (0:ℝ) (t:ℝ),((t:ℝ)-r)^α ∂volume)=
      ∫ r in (0:ℝ)..(t:ℝ),((t:ℝ)-r)^α :=
    (intervalIntegral.integral_of_le (f := fun r : ℝ => ((t:ℝ)-r)^α) t.2).symm
  have hswap : (∫ r in (0:ℝ)..(t:ℝ),((t:ℝ)-r)^α)=∫ r in (0:ℝ)..(t:ℝ),r^α := by
    simpa only [sub_self,sub_zero] using
      intervalIntegral.integral_comp_sub_left (a := 0) (b := (t:ℝ)) (fun r : ℝ => r^α) (t:ℝ)
  rw [← ho,hioc,hswap,integral_rpow (Or.inl hα),Real.zero_rpow (by linarith : α+1 ≠ 0),sub_zero]

end SHE.PredictableL2
