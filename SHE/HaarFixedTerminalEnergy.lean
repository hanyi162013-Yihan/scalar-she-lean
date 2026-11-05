module

public import SHE.TimeCausalPowers
public import SHE.HaarKernelL2Approximation

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.HaarFixedTerminalEnergy
open MeasureTheory Set PredictableL2 CircleHeat FiniteHaar HaarIntegrandEnergy
open scoped NNReal ENNReal
local instance haarFixedTerminalEnergy_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

theorem kernel_causal_power_bound {ell M : ℝ} (hell : 0 < ell) {h t s : ℝ≥0}
    (hh : (h:ℝ) ≤ 1) (ht : t ≤ h) (hs : s ≤ t) (f : EllipticField ell M) :
    ‖RealHaarIntegrand.kernel ell M hell ((t:ℝ)-(s:ℝ),f)‖^2 ≤
      singleConstant M*((t:ℝ)-(s:ℝ))^(-(1/2:ℝ)) := by
  rcases lt_or_eq_of_le hs with hs | rfl
  · apply kernel_small_bound hell (sub_pos.mpr (by exact_mod_cast hs))
    have ht' : (t:ℝ) ≤ (h:ℝ) := by exact_mod_cast ht
    linarith [s.2]
  · rw [sub_self,HaarKernelApproximation.kernel_zero hell le_rfl,norm_zero]
    simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0),Real.zero_rpow (by norm_num : -(1/2:ℝ) ≠ 0),mul_zero,le_refl]

/-- Every deterministic terminal time has finite actual convolution
energy, uniformly over arbitrary bounded elliptic state fields. -/
theorem fixed_energy_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    {h t : ℝ≥0} (hh : (h:ℝ) ≤ 1) (ht : t ≤ h)
    (f : ℝ≥0 × Ω → EllipticField ell M) :
    (∫⁻ s,∫⁻ ω,ENNReal.ofReal (‖RealHaarIntegrand.kernel ell M hell
      ((t:ℝ)-(s:ℝ),f (s,ω))‖^2) ∂μ ∂timeMeasure h) ≤
      ENNReal.ofReal (singleConstant M*(2*(t:ℝ)^(1/2:ℝ))) := by
  rw [show (∫⁻ s,∫⁻ ω,ENNReal.ofReal (‖RealHaarIntegrand.kernel ell M hell
      ((t:ℝ)-(s:ℝ),f (s,ω))‖^2) ∂μ ∂timeMeasure h)=
    ∫⁻ s,∫⁻ ω,ENNReal.ofReal (‖RealHaarIntegrand.kernel ell M hell
      ((t:ℝ)-(s:ℝ),f (s,ω))‖^2) ∂μ ∂timeMeasure t from
    HaarKernelL2Approximation.causal_lintegral hell μ f ht]
  calc
    _ ≤ ∫⁻ s,ENNReal.ofReal (singleConstant M)*ENNReal.ofReal (((t:ℝ)-(s:ℝ))^(-(1/2:ℝ))) ∂timeMeasure t := by
      apply lintegral_mono_ae
      filter_upwards [timeMeasure_ae_mem t] with s hs
      have he := lintegral_mono (μ := μ) (fun ω => ENNReal.ofReal_le_ofReal
        (kernel_causal_power_bound hell hh ht hs.2 (f (s,ω))))
      rw [ENNReal.ofReal_mul (singleConstant_nonneg hM)] at he
      simpa only [lintegral_const,measure_univ,mul_one] using he
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,causal_rpow_mass (by norm_num : (-1:ℝ) < -(1/2:ℝ))]
      norm_num only [show -(1/2:ℝ)+1=1/2 by norm_num]
      rw [← ENNReal.ofReal_mul (singleConstant_nonneg hM)]
      congr 1
      ring

end SHE.HaarFixedTerminalEnergy
