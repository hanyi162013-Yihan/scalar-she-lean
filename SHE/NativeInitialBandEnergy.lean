module

public import SHE.NativeMovingBandEnergy
public import SHE.ConvolutionEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
namespace SHE.NativeInitialBandEnergy
open Set MeasureTheory Real
open scoped ENNReal

theorem initial_window (K F : ℝ→ℝ≥0∞) (hK : Measurable K) (hF : Measurable F)
    {χ : ℝ} (hχ : 0≤χ) (hχ1 : χ≤1) (H h : ℝ) :
    (∫⁻t in Ioc (0:ℝ) (min H h),∫⁻q in Ioc (0:ℝ) t,K (t-q)*F q^χ) ≤
      (∫⁻w in Ioc (0:ℝ) h,K w)*
        ((∫⁻r in Ioc (0:ℝ) H,F r)^χ*(ENNReal.ofReal H)^(1-χ)) := by
  let K0:= (Ioc (0:ℝ) h).indicator K
  have hm:Measurable K0:=hK.indicator measurableSet_Ioc
  have he : (∫⁻t in Ioc (0:ℝ) (min H h),∫⁻q in Ioc (0:ℝ) t,K (t-q)*F q^χ)=
      ∫⁻t in Ioc (0:ℝ) (min H h),∫⁻q in Ioc (0:ℝ) t,K0 (t-q)*F q^χ := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (volume.ae_ne t)] with q hq hqt
    have htH:t≤h:=ht.2.trans (min_le_right _ _)
    have hmem:t-q∈Ioc (0:ℝ) h:=⟨by linarith [lt_of_le_of_ne hq.2 hqt],by linarith [hq.1]⟩
    rw [show K0 (t-q)=K (t-q) from indicator_of_mem hmem K]
  have hsub:Ioc (0:ℝ) (min H h)⊆Ioc (0:ℝ) H:=Ioc_subset_Ioc_right (min_le_left _ _)
  have hh: (∫⁻t in Ioc (0:ℝ) (min H h),∫⁻q in Ioc (0:ℝ) t,K0 (t-q)*F q^χ) ≤
      (∫⁻w:ℝ,K0 w)*(∫⁻r in Ioc (0:ℝ) H,F r^χ):=
    (lintegral_mono_set hsub).trans
      (causal_convolution_energy_bound K0 (fun r=>F r^χ) hm (hF.pow_const χ) H)
  have hp: (∫⁻r in Ioc (0:ℝ) H,F r^χ)≤
      (∫⁻r in Ioc (0:ℝ) H,F r)^χ*(ENNReal.ofReal H)^(1-χ):=by
    have hb:=FiniteMomentFractional.lintegral_fraction_mass
      (μ:=volume.restrict (Ioc (0:ℝ) H)) hF.aemeasurable hχ hχ1
    simpa only [Measure.restrict_apply MeasurableSet.univ,univ_inter,Real.volume_Ioc,sub_zero] using hb
  rw [he]
  refine hh.trans ?_
  rw [show (∫⁻w:ℝ,K0 w)=(∫⁻w in Ioc (0:ℝ) h,K w) from lintegral_indicator measurableSet_Ioc K]
  exact mul_le_mul_right hp _

/-- The actual initial output triangle has the same sharp current
frequency rate as complete windows. Its current energy is integrated
on the original physical clock, including the zero-past region. -/
theorem band_energy (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (hk : 0<k) (ρ χ : ℝ) (hρ : 0<ρ) (hχ0 : 0≤χ) (hχ1 : χ<1)
    (hm : χ<P.exponent+2*ρ) (η : ℝ) (hη : 0<η) :
    ∃C : ℝ,0<C ∧ ∀ν : ℝ,1≤ν→∀H : ℝ,∀F : ℝ→ℝ≥0∞,Measurable F→
      let h:=NativeBandFrequencyRates.window P.exponent ν
      ENNReal.ofReal (ν^(-2*P.exponent))*
        (∫⁻t in Ioc (0:ℝ) (min H h),∫⁻q in Ioc (0:ℝ) t,
          ENNReal.ofReal (NativeCurrentBudgetFrequency.majorant P ell Cs k ρ χ ν (t-q)^2)*F q^χ) ≤
        ENNReal.ofReal (C*ν^(-NativeBandFrequencyRates.currentDegree P.exponent ρ χ η))*
          ((∫⁻r in Ioc (0:ℝ) H,F r)^χ*(ENNReal.ofReal H)^(1-χ)) := by
  obtain ⟨Cc,Cp,hCc,hCp,hb⟩:=NativeBandFrequencyRates.band_integrals P ell Cs k hk ρ χ hρ hχ1 hm η hη
  refine ⟨Cc,hCc,?_⟩
  intro ν hν H F hF h
  let K : ℝ→ℝ≥0∞:=fun w=>ENNReal.ofReal (NativeCurrentBudgetFrequency.majorant P ell Cs k ρ χ ν w^2)
  have hKm:Measurable K:=ENNReal.measurable_ofReal.comp
    ((NativeCurrentBudgetFrequency.majorant_measurable P ell Cs k ρ χ ν).pow_const 2)
  have hi:=hb ν hν
  have hmass : ENNReal.ofReal (ν^(-2*P.exponent))*(∫⁻w in Ioc (0:ℝ) h,K w)≤
      ENNReal.ofReal (Cc*ν^(-NativeBandFrequencyRates.currentDegree P.exponent ρ χ η)) := by
    rw [←ofReal_integral_eq_lintegral_ofReal hi.1 (ae_of_all _ (fun w=>sq_nonneg _)),
      ←ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith : 0≤ν) _)]
    exact ENNReal.ofReal_le_ofReal hi.2.2.1
  have hbnd:=initial_window K F hKm hF hχ0 hχ1.le H h
  exact (mul_le_mul_right hbnd _).trans
    (by simpa only [mul_assoc] using (mul_le_mul_left hmass
      ((∫⁻r in Ioc (0:ℝ) H,F r)^χ*(ENNReal.ofReal H)^(1-χ))))

end SHE.NativeInitialBandEnergy
