module

public import SHE.NonlinearHaarIntegrand
public import SHE.TimeMeasureMass

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.HaarIntegrandEnergy
open MeasureTheory Set AddCircle CircleHeat FiniteHaar PredictableL2 RealHaarIntegrand CompanionHeat
open scoped NNReal ENNReal
local instance haarIntegrandEnergy_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

def singleConstant (M : ℝ) : ℝ := M*(1+2*HeatTrace.fractionalGaussianIntegral 0)

theorem singleConstant_nonneg {M : ℝ} (hM : 0 ≤ M) : 0 ≤ singleConstant M := by
  have hG : 0 ≤ HeatTrace.fractionalGaussianIntegral 0 :=
    (HeatTrace.fractionalGaussianIntegral_pos (by norm_num : (0:ℝ) < 1/2)).le
  unfold singleConstant
  positivity

theorem kernel_small_bound {ell M t : ℝ} (hell : 0 < ell) (ht : 0 < t) (ht1 : t ≤ 1)
    (f : EllipticField ell M) : ‖kernel ell M hell (t,f)‖^2 ≤ singleConstant M*t^(-(1/2:ℝ)) := by
  have hM : 0 ≤ M := elliptic_upper_nonneg f.1 ell M hell f.2.2
  have hs : 1 ≤ t^(-(1/2:ℝ)) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1 (by norm_num)
  rw [RealHaarIntegrand.kernel_norm_sq]
  apply (HaarHeatIntegrand.kernel_norm_sq_bound hell ht f).trans
  unfold singleConstant
  nlinarith [mul_le_mul_of_nonneg_left hs hM]

theorem kernel_causal_bound {ell M : ℝ} (hell : 0 < ell) {h t s : ℝ≥0}
    (hh : (h:ℝ) ≤ 1) (ht : t ≤ h) (hs : s < t) (f : EllipticField ell M) :
    ENNReal.ofReal (‖kernel ell M hell ((t:ℝ)-(s:ℝ),f)‖^2) ≤
      ENNReal.ofReal (singleConstant M)*picardKernel (h:ℝ) ((t:ℝ)-(s:ℝ)) := by
  have hτ : 0 < (t:ℝ)-(s:ℝ) := sub_pos.mpr (by exact_mod_cast hs)
  have hτh : (t:ℝ)-(s:ℝ) ≤ (h:ℝ) := by
    have ht' : (t:ℝ) ≤ (h:ℝ) := by exact_mod_cast ht
    linarith [s.2]
  have hk : picardKernel (h:ℝ) ((t:ℝ)-(s:ℝ))=ENNReal.ofReal (((t:ℝ)-(s:ℝ))^(-(1/2:ℝ))) := by
    unfold picardKernel
    exact Set.indicator_of_mem (show (t:ℝ)-(s:ℝ) ∈ Ioc 0 (h:ℝ) from ⟨hτ,hτh⟩) _
  rw [hk,← ENNReal.ofReal_mul (singleConstant_nonneg (elliptic_upper_nonneg f.1 ell M hell f.2.2))]
  exact ENNReal.ofReal_le_ofReal (kernel_small_bound hell hτ (hτh.trans hh) f)

/-- The literal real Hilbert-valued common-Haar integrand has finite
total stochastic-convolution energy on every bounded short interval,
uniformly over arbitrary predictable states. -/
theorem total_energy_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M) (h : ℝ≥0) (hh : (h:ℝ) ≤ 1)
    (f : ℝ≥0 × Ω → EllipticField ell M) :
    (∫⁻ t,∫⁻ s,∫⁻ ω,ENNReal.ofReal (‖kernel ell M hell ((t:ℝ)-(s:ℝ),f (s,ω))‖^2)
      ∂μ ∂timeMeasure t ∂timeMeasure h) ≤
      ENNReal.ofReal (singleConstant M*(2*(h:ℝ)^(1/2:ℝ))*(h:ℝ)) := by
  let C := ENNReal.ofReal (singleConstant M)
  have hb : (∫⁻ t,∫⁻ s,∫⁻ ω,ENNReal.ofReal (‖kernel ell M hell ((t:ℝ)-(s:ℝ),f (s,ω))‖^2)
      ∂μ ∂timeMeasure t ∂timeMeasure h) ≤
      ∫⁻ t,∫⁻ s,C*picardKernel (h:ℝ) ((t:ℝ)-(s:ℝ))*1 ∂timeMeasure t ∂timeMeasure h := by
    apply lintegral_mono_ae
    filter_upwards [timeMeasure_ae_mem h] with t ht
    apply lintegral_mono_ae
    filter_upwards [timeMeasure_ae_mem t,(timeMeasure t).ae_ne t] with s hs hst
    have hs' : s < t := lt_of_le_of_ne hs.2 hst
    have he := lintegral_mono (μ := μ) (fun ω => kernel_causal_bound hell hh ht.2 hs' (f (s,ω)))
    simpa only [lintegral_const,measure_univ,mul_one] using he
  calc
    _ ≤ _ := hb
    _ = C*(∫⁻ t,∫⁻ s,picardKernel (h:ℝ) ((t:ℝ)-(s:ℝ))*1 ∂timeMeasure t ∂timeMeasure h) := by
      simp_rw [mul_assoc,lintegral_const_mul' C _ ENNReal.ofReal_ne_top]
    _ ≤ C*(ENNReal.ofReal (2*(h:ℝ)^(1/2:ℝ))*(∫⁻ _ : ℝ≥0,(1:ℝ≥0∞) ∂timeMeasure h)) :=
      mul_le_mul_right (predictable_picard_causal_energy h (fun _ => 1) measurable_const) C
    _ = _ := by
      rw [timeMeasure_one_integral]
      dsimp only [C]
      rw [← mul_assoc,← ENNReal.ofReal_mul (singleConstant_nonneg hM),
        ← ENNReal.ofReal_mul (mul_nonneg (singleConstant_nonneg hM) (by positivity))]

theorem total_energy_finite {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M) (h : ℝ≥0) (hh : (h:ℝ) ≤ 1)
    (f : ℝ≥0 × Ω → EllipticField ell M) :
    (∫⁻ t,∫⁻ s,∫⁻ ω,ENNReal.ofReal (‖kernel ell M hell ((t:ℝ)-(s:ℝ),f (s,ω))‖^2)
      ∂μ ∂timeMeasure t ∂timeMeasure h) < ∞ :=
  (total_energy_bound μ hell hM h hh f).trans_lt ENNReal.ofReal_lt_top

theorem nonlinear_total_energy_finite {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {a : ℝ → ℝ} (ha : Measurable a) {ell M : ℝ} (hell : 0 < ell)
    (hb : ∀ z,ell ≤ a z ∧ a z ≤ M) (h : ℝ≥0) (hh : (h:ℝ) ≤ 1)
    (u : ℝ≥0 × Ω → LowBands.StateL2) :
    (∫⁻ t,∫⁻ s,∫⁻ ω,ENNReal.ofReal
      (‖NonlinearHaarIntegrand.kernel a ha ell M hell hb ((t:ℝ)-(s:ℝ),u (s,ω))‖^2)
      ∂μ ∂timeMeasure t ∂timeMeasure h) < ∞ :=
  total_energy_finite μ hell (hell.le.trans ((hb 0).1.trans (hb 0).2)) h hh
    (fun p => NonlinearHaarIntegrand.coefficientField a ha ell M hell hb (u p))

end SHE.HaarIntegrandEnergy
