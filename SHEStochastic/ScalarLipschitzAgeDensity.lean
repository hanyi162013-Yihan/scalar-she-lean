module

public import SHEStochastic.ScalarLipschitzWeightedMoment

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.ScalarLipschitzAgeDensity
open MeasureTheory Set SHE SHE.PredictableL2
open scoped NNReal ENNReal

/-- The true old and new portions of the stochastic convolution's
time increment. The split is at the earlier observation time. -/
def density (K : ℝ) (s t r : ℝ≥0) : ℝ≥0∞ :=
  if r<s then ENNReal.ofReal (K*((t : ℝ)-(s : ℝ))^(1/4 : ℝ)*
      ((s : ℝ)-(r : ℝ))^(-(3/4 : ℝ)))
  else if r<t then ENNReal.ofReal (K*((t : ℝ)-(r : ℝ))^(-(1/2 : ℝ)))
  else 0

theorem measurable (K : ℝ) (s t : ℝ≥0) : Measurable (density K s t) := by
  unfold density
  apply Measurable.ite measurableSet_Iio
  · fun_prop
  · apply Measurable.ite measurableSet_Iio <;> fun_prop

theorem mass {K : ℝ} (hK : 0≤K) {H s t : ℝ≥0} (hst : s≤t) (ht : t≤H) :
    (∫⁻ r,density K s t r ∂timeMeasure H)≤
      ENNReal.ofReal (6*K*(H : ℝ)^(1/4 : ℝ)*((t : ℝ)-(s : ℝ))^(1/4 : ℝ)) := by
  let d := (t : ℝ)-(s : ℝ)
  have hd : 0≤d := sub_nonneg.mpr (by exact_mod_cast hst)
  have hdH : d≤(H : ℝ) :=
    (sub_le_self _ s.property).trans (by exact_mod_cast ht)
  have hA : 0≤K*d^(1/4 : ℝ) := mul_nonneg hK (Real.rpow_nonneg hd _)
  have hzero (r : ℝ≥0) (hr : t<r) : density K s t r=0 := by
    rw [density,ite_eq_right (not_lt_of_ge (hst.trans hr.le)),ite_eq_right hr.not_gt]
  rw [causal_lintegral_of_zero ht _ hzero,timeMeasure_split hst,lintegral_add_measure]
  have ho :
      (∫⁻ r,density K s t r ∂timeMeasure s)=
        ENNReal.ofReal (K*d^(1/4 : ℝ)*(4*(s : ℝ)^(1/4 : ℝ))) := by
    calc
      _ = ∫⁻ r,ENNReal.ofReal (K*d^(1/4 : ℝ))*
          ENNReal.ofReal (((s : ℝ)-(r : ℝ))^(-(3/4 : ℝ))) ∂timeMeasure s := by
        apply lintegral_congr_ae
        filter_upwards [timeMeasure_ae_mem s,(timeMeasure s).ae_ne s] with r hr hne
        rw [density,ite_eq_left (lt_of_le_of_ne hr.2 hne),←ENNReal.ofReal_mul hA]
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          causal_rpow_mass (by norm_num : (-1 : ℝ)< -(3/4 : ℝ))]
        norm_num only [show -(3/4 : ℝ)+1=1/4 by norm_num]
        rw [←ENNReal.ofReal_mul hA]
        congr 1
        ring
  have hn :
      (∫⁻ r,density K s t r ∂intervalTimeMeasure s t)≤
        ENNReal.ofReal (K*(2*d^(1/2 : ℝ))) := by
    calc
      _ ≤ ∫⁻ r,ENNReal.ofReal K*
          ENNReal.ofReal (((t : ℝ)-(r : ℝ))^(-(1/2 : ℝ))) ∂intervalTimeMeasure s t := by
        apply lintegral_mono_ae
        filter_upwards [intervalTimeMeasure_ae_mem s ht] with r hr
        rw [density,ite_eq_right hr.1.not_gt]
        by_cases h : r<t
        · rw [ite_eq_left h,←ENNReal.ofReal_mul hK]
        · simp only [ite_eq_right h,zero_le]
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          interval_causal_rpow_mass (by norm_num : (-1 : ℝ)< -(1/2 : ℝ)) hst]
        norm_num only [show -(1/2 : ℝ)+1=1/2 by norm_num]
        rw [←ENNReal.ofReal_mul hK]
        congr 1
        ring
  rw [ho]
  apply (add_le_add le_rfl hn).trans
  rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hsH : (s : ℝ)^(1/4 : ℝ)≤(H : ℝ)^(1/4 : ℝ) :=
    Real.rpow_le_rpow s.property (by exact_mod_cast hst.trans ht) (by norm_num)
  have hδ : d^(1/2 : ℝ)≤(H : ℝ)^(1/4 : ℝ)*d^(1/4 : ℝ) := by
    rw [show (1/2 : ℝ)=1/4+1/4 by norm_num]
    rw [Real.rpow_add' hd (by norm_num)]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hd hdH (by norm_num))
      (Real.rpow_nonneg hd _)
  nlinarith only [mul_le_mul_of_nonneg_left hsH hA,mul_le_mul_of_nonneg_left hδ hK]

end SHEStochastic.ScalarLipschitzAgeDensity
