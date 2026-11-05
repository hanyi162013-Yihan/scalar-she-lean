module

public import SHEStochastic.CausalHeatIncrementEnergy
public import SHE.BieleckiColumnEnergy
public import Mathlib.MeasureTheory.Integral.MeanInequalities

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarLipschitzWeightedMoment
open MeasureTheory Set SHE SHE.PredictableL2
open scoped NNReal ENNReal

/-- Jensen with the deterministic heat age as its density. Time is
integrated before probability, with no independence assumption. -/
theorem weighted_eighth {T Ω : Type*} [MeasurableSpace T] [MeasurableSpace Ω]
    (η : Measure T) (μ : Measure Ω) [SFinite η] [SFinite μ]
    (k : T → ℝ≥0∞) (hk : Measurable k)
    (f : T×Ω → ℝ≥0∞) (hf : Measurable f) (M : ℝ≥0∞)
    (hM : ∀ᵐ s ∂η,(∫⁻ ω,(f (s,ω))^8 ∂μ)≤M) :
    (∫⁻ ω,(∫⁻ s,k s*f (s,ω) ∂η)^8 ∂μ)≤(∫⁻ s,k s ∂η)^8*M := by
  let ν := η.withDensity k
  have hmass : ν univ = ∫⁻ s,k s ∂η := by simp only [ν,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  have hJ (ω : Ω) : (∫⁻ s,k s*f (s,ω) ∂η)^8≤
      (∫⁻ s,k s ∂η)^7*(∫⁻ s,k s*(f (s,ω))^8 ∂η) := by
    have hsec : Measurable (fun s => f (s,ω)) := hf.comp (measurable_id.prodMk measurable_const)
    have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq ν
      (p := 8) (q := 8/7) (Real.holderConjugate_iff.mpr (by norm_num))
      (f := fun s => f (s,ω)) (g := fun _ => 1) hsec.aemeasurable aemeasurable_const
    simp only [Pi.mul_apply,mul_one,ENNReal.one_rpow,lintegral_const,one_mul] at hh
    have hp := pow_le_pow_left' hh 8
    rw [mul_pow,←ENNReal.rpow_mul_natCast,←ENNReal.rpow_mul_natCast] at hp
    norm_num only [show (1/8 : ℝ)*8=1 by norm_num,show (1/(8/7) : ℝ)*8=7 by norm_num,
      ENNReal.rpow_one] at hp
    rw [show (7 : ℝ)=(7 : ℕ) by norm_num,ENNReal.rpow_natCast,hmass] at hp
    rw [show (8 : ℝ)=(8 : ℕ) by norm_num] at hp
    simp only [ENNReal.rpow_natCast] at hp
    rw [lintegral_withDensity_eq_lintegral_mul _ hk hsec,
      lintegral_withDensity_eq_lintegral_mul _ hk (hsec.pow_const _),mul_comm] at hp
    simpa only [Pi.mul_apply,mul_comm] using hp
  have hm : Measurable (fun p : T×Ω => k p.1*(f p)^8) :=
    (hk.comp measurable_fst).mul (hf.pow_const _)
  calc
    _ ≤ ∫⁻ ω,(∫⁻ s,k s ∂η)^7*(∫⁻ s,k s*(f (s,ω))^8 ∂η) ∂μ :=
      lintegral_mono hJ
    _ = (∫⁻ s,k s ∂η)^7*(∫⁻ s,k s*(∫⁻ ω,(f (s,ω))^8 ∂μ) ∂η) := by
      have hs := lintegral_lintegral_swap (μ := η) (ν := μ) (f := fun s ω => k s*(f (s,ω))^8) hm.aemeasurable
      have hinner : Measurable (fun ω => ∫⁻ s,k s*(f (s,ω))^8 ∂η) :=
        (hm.comp (measurable_snd.prodMk measurable_fst)).lintegral_prod_right'
      rw [lintegral_const_mul'' ((∫⁻ s,k s ∂η)^7) hinner.aemeasurable,←hs]
      congr 1
      apply lintegral_congr
      intro s
      exact lintegral_const_mul'' _ ((hf.comp (measurable_const.prodMk measurable_id)).pow_const _).aemeasurable
    _ ≤ (∫⁻ s,k s ∂η)^7*(∫⁻ s,k s*M ∂η) :=
      mul_le_mul_right (lintegral_mono_ae (hM.mono (fun s h => mul_le_mul_right h (k s)))) _
    _ = _ := by rw [lintegral_mul_const'' _ hk.aemeasurable,←mul_assoc,←pow_succ]

/-- The exact Bielecki density on the original finite time measure
has mass at most the positive half-power heat resolvent. -/
theorem damped_mass (H : ℝ≥0) {γ : ℝ} (hγ : 0<γ) {t : ℝ≥0} (ht : t≤H) :
    (∫⁻ s,BieleckiKernel.kernel H γ ((t : ℝ)-(s : ℝ)) ∂timeMeasure H)≤
      ENNReal.ofReal (BieleckiKernel.mass γ) := by
  rw [causal_lintegral_of_zero ht]
  · rw [timeMeasure_lintegral]
    calc
      _ = ∫⁻ r in Ioc (0 : ℝ) t,BieleckiKernel.kernel H γ ((t : ℝ)-r) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        rw [Real.coe_toNNReal _ hr.1.le]
      _ ≤ ∫⁻ r : ℝ,BieleckiKernel.kernel H γ ((t : ℝ)-r) := lintegral_mono' Measure.restrict_le_self le_rfl
      _ = ∫⁻ r : ℝ,BieleckiKernel.kernel H γ r := by
        rw [lintegral_sub_left_eq_self]
      _ ≤ _ := BieleckiKernel.kernel_mass_le (H : ℝ) hγ
  · intro s hs
    unfold BieleckiKernel.kernel
    exact indicator_of_notMem (fun hm => (not_lt_of_ge
      (sub_nonpos.mpr (by exact_mod_cast hs.le))) hm.1) _

end SHEStochastic.ScalarLipschitzWeightedMoment
