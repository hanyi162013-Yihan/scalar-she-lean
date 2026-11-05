module

public import SHE.IntervalTimeMeasure

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1100000
noncomputable section

namespace SHE.PastRelativeEnergy
open Set MeasureTheory PredictableL2
open scoped NNReal ENNReal

/-- Exact physical time change from a post-v bracket inside the original
full-horizon noise space to the genuine relative interval [0,b-v]. -/
theorem indicator_lintegral (H v b : ℝ≥0) (hvb : v≤b) (hbH : b≤H)
    (F : ℝ → ℝ) (hF : IntervalIntegrable F volume 0 ((b:ℝ)-(v:ℝ)))
    (hF0 : ∀ r,0≤F r) :
    (∫⁻ r,(Ioc v b).indicator (fun r : ℝ≥0 => ENNReal.ofReal (F ((r:ℝ)-(v:ℝ)))) r ∂timeMeasure H)=
      ENNReal.ofReal (∫ s in (0:ℝ)..((b:ℝ)-(v:ℝ)),F s) := by
  rw [lintegral_indicator measurableSet_Ioc,timeMeasure_restrict_Ioc v hbH,intervalTimeMeasure_lintegral]
  have he : (∫⁻ r in Ioc (v:ℝ) (b:ℝ),ENNReal.ofReal (F ((r.toNNReal:ℝ)-(v:ℝ))))=
      ∫⁻ r in Ioc (v:ℝ) (b:ℝ),ENNReal.ofReal (F (r-(v:ℝ))) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [Real.coe_toNNReal _ (v.2.trans_lt hr.1).le]
  rw [he]
  have hshift : IntervalIntegrable (fun r => F (r-(v:ℝ))) volume (v:ℝ) (b:ℝ) := by
    simpa only [zero_add,sub_add_cancel] using hF.comp_sub_right (v:ℝ)
  have horder : (v:ℝ)≤(b:ℝ) := by exact_mod_cast hvb
  rw [←ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le horder).mp hshift)
    (Filter.Eventually.of_forall (fun r => hF0 (r-(v:ℝ)))),
    ←intervalIntegral.integral_of_le horder,
    intervalIntegral.integral_comp_sub_right]
  simp only [sub_self]

end SHE.PastRelativeEnergy
