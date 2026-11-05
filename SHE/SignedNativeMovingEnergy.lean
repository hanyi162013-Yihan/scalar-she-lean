module

public import SHE.SignedNativeBandFrequency
public import SHE.NativeInitialBandEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace SHE.SignedNativeBandFrequency
open Set MeasureTheory Real
open scoped ENNReal

/-- The signed endpoint row has genuine current-energy convolution on
both complete windows and the initial triangle. Its arbitrary bad tail
is integrated on the same physical horizon, without a current bound. -/
theorem moving_energy (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(Cs:ℕ→ℝ)
    (k:ℕ)(hk:0<k)(ρ η ε tail ζ:ℝ)(hα:0<ρ+η)(hαhalf:ρ+η<1/2)(hζ:0<ζ):
    ∃Cg Cb:ℝ,0<Cg ∧ 0<Cb ∧ ∀ν:ℝ,1≤ν→∀H:ℝ,∀F:ℝ→ℝ≥0∞,Measurable F→
      let h:=NativeBandFrequencyRates.window P.exponent ν
      let Kg:=fun s=>ENNReal.ofReal (NativeCurrentBudgetFrequency.majorant P ell Cs k (ρ+η) (2*(ρ+η)) ν (h-s)^2)
      let Kb:=fun s=>ENNReal.ofReal (NativeCurrentBudgetFrequency.majorant P ell Cs k 0 0 ν (h-s)^2)
      ENNReal.ofReal (ν^(-2*P.exponent+2*ε))*
        (∫⁻v in Ioc (0:ℝ) (H-h),∫⁻s in Ioc (0:ℝ) h,Kg s*F (v+s))≤
          ENNReal.ofReal (Cg*ν^(-goodDegree P.exponent ε ζ))*(∫⁻r in Ioc (0:ℝ) H,F r) ∧
      ENNReal.ofReal (ν^(-2*P.exponent+2*ε))*
        (∫⁻t in Ioc (0:ℝ) (min H h),∫⁻q in Ioc (0:ℝ) t,
          ENNReal.ofReal (NativeCurrentBudgetFrequency.majorant P ell Cs k (ρ+η) (2*(ρ+η)) ν (t-q)^2)*F q)≤
          ENNReal.ofReal (Cg*ν^(-goodDegree P.exponent ε ζ))*(∫⁻r in Ioc (0:ℝ) H,F r) ∧
      ENNReal.ofReal (ν^(-2*P.exponent-tail))*(∫⁻v in Ioc (0:ℝ) (H-h),∫⁻s in Ioc (0:ℝ) h,Kb s)≤
          ENNReal.ofReal (Cb*ν^(-badDegree P.exponent tail ζ))*ENNReal.ofReal H ∧
      ENNReal.ofReal (ν^(-2*P.exponent-tail))*
        (∫⁻t in Ioc (0:ℝ) (min H h),∫⁻q in Ioc (0:ℝ) t,
          ENNReal.ofReal (NativeCurrentBudgetFrequency.majorant P ell Cs k 0 0 ν (t-q)^2))≤
          ENNReal.ofReal (Cb*ν^(-badDegree P.exponent tail ζ))*ENNReal.ofReal H:=by
  obtain ⟨Cg,Cb,hCg,hCb,hb⟩:=band_integrals P ell Cs k hk ρ η ε tail ζ hα hαhalf hζ
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro ν hν H F hF h Kg Kb
  have hv:0<ν:=zero_lt_one.trans_le hν
  have hh:0<h:=NativeBandFrequencyRates.window_pos hv
  have hi:=hb ν hν
  have hgr:=NativeMovingBandEnergy.reflected_integral hh.le hi.1
  have hbr:=NativeMovingBandEnergy.reflected_integral hh.le hi.2.1
  let G:=fun w=>ENNReal.ofReal (NativeCurrentBudgetFrequency.majorant P ell Cs k (ρ+η) (2*(ρ+η)) ν w^2)
  let B:=fun w=>ENNReal.ofReal (NativeCurrentBudgetFrequency.majorant P ell Cs k 0 0 ν w^2)
  have hG:Measurable G:=ENNReal.measurable_ofReal.comp
    ((NativeCurrentBudgetFrequency.majorant_measurable P ell Cs k (ρ+η) (2*(ρ+η)) ν).pow_const 2)
  have hB:Measurable B:=ENNReal.measurable_ofReal.comp
    ((NativeCurrentBudgetFrequency.majorant_measurable P ell Cs k 0 0 ν).pow_const 2)
  have hKg:Measurable Kg:=hG.comp (measurable_const.sub measurable_id)
  have hKb:Measurable Kb:=by
    exact (ENNReal.measurable_ofReal.comp
      ((NativeCurrentBudgetFrequency.majorant_measurable P ell Cs k 0 0 ν).pow_const 2)).comp
        (measurable_const.sub measurable_id)
  have hg0 : ENNReal.ofReal (ν^(-2*P.exponent+2*ε))*(∫⁻w in Ioc (0:ℝ) h,G w)≤
      ENNReal.ofReal (Cg*ν^(-goodDegree P.exponent ε ζ)):=by
    rw [←ofReal_integral_eq_lintegral_ofReal hi.1 (ae_of_all _ (fun _=>sq_nonneg _)),
      ←ENNReal.ofReal_mul (rpow_nonneg hv.le _)]
    exact ENNReal.ofReal_le_ofReal hi.2.2.1
  have hb0 : ENNReal.ofReal (ν^(-2*P.exponent-tail))*(∫⁻w in Ioc (0:ℝ) h,B w)≤
      ENNReal.ofReal (Cb*ν^(-badDegree P.exponent tail ζ)):=by
    rw [←ofReal_integral_eq_lintegral_ofReal hi.2.1 (ae_of_all _ (fun _=>sq_nonneg _)),
      ←ENNReal.ofReal_mul (rpow_nonneg hv.le _)]
    exact ENNReal.ofReal_le_ofReal hi.2.2.2
  have hgmass : ENNReal.ofReal (ν^(-2*P.exponent+2*ε))*(∫⁻s in Ioc (0:ℝ) h,Kg s)≤
      ENNReal.ofReal (Cg*ν^(-goodDegree P.exponent ε ζ)):=by
    rw [←ofReal_integral_eq_lintegral_ofReal hgr.1 (ae_of_all _ (fun _=>sq_nonneg _)),
      ←ENNReal.ofReal_mul (rpow_nonneg hv.le _),hgr.2]
    exact ENNReal.ofReal_le_ofReal hi.2.2.1
  have hbmass : ENNReal.ofReal (ν^(-2*P.exponent-tail))*(∫⁻s in Ioc (0:ℝ) h,Kb s)≤
      ENNReal.ofReal (Cb*ν^(-badDegree P.exponent tail ζ)):=by
    rw [←ofReal_integral_eq_lintegral_ofReal hbr.1 (ae_of_all _ (fun _=>sq_nonneg _)),
      ←ENNReal.ofReal_mul (rpow_nonneg hv.le _),hbr.2]
    exact ENNReal.ofReal_le_ofReal hi.2.2.2
  have hgcomp : (∫⁻v in Ioc (0:ℝ) (H-h),∫⁻s in Ioc (0:ℝ) h,Kg s*F (v+s))≤
      (∫⁻s in Ioc (0:ℝ) h,Kg s)*(∫⁻r in Ioc (0:ℝ) H,F r):=by
    simpa only [ENNReal.rpow_one,sub_self,ENNReal.rpow_zero,mul_one] using
      NativeMovingBandEnergy.complete_current Kg F hKg hF (χ:=1) (by norm_num) (by norm_num) hh.le H
  have hginit : (∫⁻t in Ioc (0:ℝ) (min H h),∫⁻q in Ioc (0:ℝ) t,G (t-q)*F q)≤
      (∫⁻w in Ioc (0:ℝ) h,G w)*(∫⁻r in Ioc (0:ℝ) H,F r):=by
    simpa only [ENNReal.rpow_one,sub_self,ENNReal.rpow_zero,mul_one] using
      NativeInitialBandEnergy.initial_window G F hG hF (χ:=1) (by norm_num) (by norm_num) H h
  have hbcomp : (∫⁻v in Ioc (0:ℝ) (H-h),∫⁻s in Ioc (0:ℝ) h,Kb s)≤
      (∫⁻s in Ioc (0:ℝ) h,Kb s)*ENNReal.ofReal H:=by
    simpa only [mul_one,lintegral_one,Measure.restrict_apply MeasurableSet.univ,univ_inter,Real.volume_Ioc,sub_zero] using
      NativeMovingBandEnergy.complete_past Kb (fun _=>1) hKb measurable_const hh.le H
  have hbinit : (∫⁻t in Ioc (0:ℝ) (min H h),∫⁻q in Ioc (0:ℝ) t,B (t-q))≤
      (∫⁻w in Ioc (0:ℝ) h,B w)*ENNReal.ofReal H:=by
    simpa only [ENNReal.rpow_one,sub_self,ENNReal.rpow_zero,mul_one,lintegral_one,
      Measure.restrict_apply MeasurableSet.univ,univ_inter,Real.volume_Ioc,sub_zero] using
      NativeInitialBandEnergy.initial_window B (fun _=>1) hB measurable_const (χ:=1) (by norm_num) (by norm_num) H h
  refine ⟨?_,?_,?_,?_⟩
  · exact (mul_le_mul_right hgcomp _).trans
      (by simpa only [mul_assoc] using (mul_le_mul_left hgmass (∫⁻r in Ioc (0:ℝ) H,F r)))
  · exact (mul_le_mul_right hginit _).trans
      (by simpa only [mul_assoc] using (mul_le_mul_left hg0 (∫⁻r in Ioc (0:ℝ) H,F r)))
  · exact (mul_le_mul_right hbcomp _).trans
      (by simpa only [mul_assoc] using (mul_le_mul_left hbmass (ENNReal.ofReal H)))
  · exact (mul_le_mul_right hbinit _).trans
      (by simpa only [mul_assoc] using (mul_le_mul_left hb0 (ENNReal.ofReal H)))

end SHE.SignedNativeBandFrequency
