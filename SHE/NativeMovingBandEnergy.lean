module

public import SHE.NativeBandFrequencyRates
public import SHE.MovingPastFractional

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
namespace SHE.NativeMovingBandEnergy
open Set MeasureTheory Real
open scoped ENNReal

theorem reflected_integral {g : ℝ→ℝ} {h : ℝ} (hh : 0≤h)
    (hi : Integrable g (volume.restrict (Ioc 0 h))) :
    Integrable (fun s=>g (h-s)) (volume.restrict (Ioc 0 h)) ∧
      (∫s,g (h-s) ∂volume.restrict (Ioc 0 h))=∫w,g w ∂volume.restrict (Ioc 0 h) := by
  have hg : IntervalIntegrable g volume 0 h :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hh).mpr hi
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hh).mp ?_,?_⟩
  · simpa only [sub_zero,sub_self] using (hg.comp_sub_left h).symm
  · rw [←intervalIntegral.integral_of_le hh,←intervalIntegral.integral_of_le hh]
    simpa only [sub_zero,sub_self] using
      intervalIntegral.integral_comp_sub_left g h (a:=0) (b:=h)

theorem complete_current (K F : ℝ→ℝ≥0∞) (hK : Measurable K)
    (hF : Measurable F) {χ h : ℝ} (hχ : 0≤χ) (hχ1 : χ≤1) (hh : 0≤h) (H : ℝ) :
    (∫⁻v in Ioc (0:ℝ) (H-h),∫⁻s in Ioc (0:ℝ) h,K s*F (v+s)^χ) ≤
      (∫⁻s in Ioc (0:ℝ) h,K s)*
        ((∫⁻r in Ioc (0:ℝ) H,F r)^χ*(ENNReal.ofReal H)^(1-χ)) := by
  have he : (∫⁻v in Ioc (0:ℝ) (H-h),∫⁻s in Ioc (0:ℝ) h,K s*F (v+s)^χ)=
      ∫⁻v in Ioc (0:ℝ) (H-h),∫⁻s in Ioc (0:ℝ) h,
        K s*MovingPastFractional.powerWindow H χ F (v+s) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [MovingPastFractional.powerWindow,indicator_of_mem
      (show v+s∈Ioc (0:ℝ) H from ⟨by linarith [hv.1,hs.1],by linarith [hv.2,hs.2]⟩)]
  rw [he]
  have hsub : Ioc (0:ℝ) (H-h) ⊆ Ioc (0:ℝ) H := fun _ hv=>⟨hv.1,by linarith [hv.2]⟩
  exact (lintegral_mono_set hsub).trans
    (MovingPastFractional.current_window K F hK hF hχ hχ1 H h)

theorem complete_past (K F : ℝ→ℝ≥0∞) (hK : Measurable K)
    (hF : Measurable F) {h : ℝ} (hh : 0≤h) (H : ℝ) :
    (∫⁻v in Ioc (0:ℝ) (H-h),∫⁻s in Ioc (0:ℝ) h,K s*F v) ≤
      (∫⁻s in Ioc (0:ℝ) h,K s)*(∫⁻r in Ioc (0:ℝ) H,F r) := by
  have hb:=MovingPastFractional.past_window K F hK hF
    (χ:=1) (by norm_num) (by norm_num) H h
  have hsub : Ioc (0:ℝ) (H-h) ⊆ Ioc (0:ℝ) H := fun _ hv=>⟨hv.1,by linarith [hv.2]⟩
  simpa only [ENNReal.rpow_one,sub_self,ENNReal.rpow_zero,mul_one] using
    (lintegral_mono_set hsub).trans hb

/-- The actual completed windows retain the true global current energy
and past energy. Root-band amplitude is included, and neither input is
replaced by a time supremum. Constants precede every band and horizon. -/
theorem band_energy (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (hk : 0<k) (ρ χ : ℝ) (hρ : 0<ρ) (hχ0 : 0≤χ) (hχ1 : χ<1)
    (hm : χ<P.exponent+2*ρ) (η : ℝ) (hη : 0<η) :
    ∃Cc Cp : ℝ,0<Cc ∧ 0<Cp ∧ ∀ν : ℝ,1≤ν→∀H : ℝ,
      ∀F : ℝ→ℝ≥0∞,Measurable F→
      let h:=NativeBandFrequencyRates.window P.exponent ν
      ENNReal.ofReal (ν^(-2*P.exponent)) *
        (∫⁻v in Ioc (0:ℝ) (H-h),∫⁻s in Ioc (0:ℝ) h,
          ENNReal.ofReal (NativeCurrentBudgetFrequency.majorant P ell Cs k ρ χ ν (h-s)^2)*F (v+s)^χ) ≤
        ENNReal.ofReal (Cc*ν^(-NativeBandFrequencyRates.currentDegree P.exponent ρ χ η))*
          ((∫⁻r in Ioc (0:ℝ) H,F r)^χ*(ENNReal.ofReal H)^(1-χ)) ∧
      ENNReal.ofReal (ν^(-2*P.exponent)) *
        (∫⁻v in Ioc (0:ℝ) (H-h),∫⁻s in Ioc (0:ℝ) h,
          ENNReal.ofReal (s^(-(1/2:ℝ))*NativeCurrentBudgetFrequency.majorant P ell Cs k ρ 0 ν (h-s)^2)*F v) ≤
        ENNReal.ofReal (Cp*ν^(-NativeBandFrequencyRates.pastDegree P.exponent η))*
          (∫⁻r in Ioc (0:ℝ) H,F r) := by
  obtain ⟨Cc,Cp,hCc,hCp,hb⟩:=NativeBandFrequencyRates.band_integrals P ell Cs k hk ρ χ hρ hχ1 hm η hη
  refine ⟨Cc,Cp,hCc,hCp,?_⟩
  intro ν hν H F hF h
  have hh:0<h:=NativeBandFrequencyRates.window_pos (lt_of_lt_of_le zero_lt_one hν)
  have hi:=hb ν hν
  have hc:=reflected_integral hh.le hi.1
  let Kc : ℝ→ℝ≥0∞:=fun s=>ENNReal.ofReal (NativeCurrentBudgetFrequency.majorant P ell Cs k ρ χ ν (h-s)^2)
  let Kp : ℝ→ℝ≥0∞:=fun s=>ENNReal.ofReal (s^(-(1/2:ℝ))*NativeCurrentBudgetFrequency.majorant P ell Cs k ρ 0 ν (h-s)^2)
  have hcm:Measurable Kc:=ENNReal.measurable_ofReal.comp
    (((NativeCurrentBudgetFrequency.majorant_measurable P ell Cs k ρ χ ν).comp
      (measurable_const.sub measurable_id)).pow_const 2)
  have hpm:Measurable Kp:=ENNReal.measurable_ofReal.comp
    ((measurable_id.pow_const (-(1/2:ℝ))).mul
      (((NativeCurrentBudgetFrequency.majorant_measurable P ell Cs k ρ 0 ν).comp
        (measurable_const.sub measurable_id)).pow_const 2))
  have hmassc : ENNReal.ofReal (ν^(-2*P.exponent))*(∫⁻s in Ioc (0:ℝ) h,Kc s)≤
      ENNReal.ofReal (Cc*ν^(-NativeBandFrequencyRates.currentDegree P.exponent ρ χ η)) := by
    rw [←ofReal_integral_eq_lintegral_ofReal hc.1 (ae_of_all _ (fun s=>sq_nonneg _)),
      ←ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith : 0≤ν) _),hc.2]
    exact ENNReal.ofReal_le_ofReal hi.2.2.1
  have hmassp : ENNReal.ofReal (ν^(-2*P.exponent))*(∫⁻s in Ioc (0:ℝ) h,Kp s)≤
      ENNReal.ofReal (Cp*ν^(-NativeBandFrequencyRates.pastDegree P.exponent η)) := by
    have hp0 : ∀ᵐs:ℝ ∂volume.restrict (Ioc 0 h),
        0≤s^(-(1/2:ℝ))*NativeCurrentBudgetFrequency.majorant P ell Cs k ρ 0 ν (h-s)^2 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact mul_nonneg (Real.rpow_nonneg hs.1.le _) (sq_nonneg _)
    rw [←ofReal_integral_eq_lintegral_ofReal hi.2.1 hp0]
    rw [←ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith : 0≤ν) _)]
    exact ENNReal.ofReal_le_ofReal hi.2.2.2
  constructor
  · have hmoving:=complete_current Kc F hcm hF hχ0 hχ1.le hh.le H
    exact (mul_le_mul_right hmoving _).trans
      (by simpa only [mul_assoc] using (mul_le_mul_left hmassc
        ((∫⁻r in Ioc (0:ℝ) H,F r)^χ*(ENNReal.ofReal H)^(1-χ))))
  · have hmoving:=complete_past Kp F hpm hF hh.le H
    exact (mul_le_mul_right hmoving _).trans
      (by simpa only [mul_assoc] using (mul_le_mul_left hmassp (∫⁻r in Ioc (0:ℝ) H,F r)))

end SHE.NativeMovingBandEnergy
