module

public import SHEStochastic.CausalKernelInput
public import SHE.PredictableTime

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.CausalKernelComparison
open MeasureTheory Set SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω C V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup C] [NormedAddCommGroup V]
    [MeasurableSpace V] [BorelSpace V]

/-- A dimension-independent predictable L2 comparison for any causal
kernel with the heat singularity. It reuses the scalar Volterra bound. -/
theorem expected_energy (μ : Measure Ω) [SFinite μ] (H : ℝ≥0) (hH : (H : ℝ) ≤ 1)
    (K : ℝ → (ℝ≥0 × Ω) → C) (W : ℝ≥0 × Ω → V) (hW : Measurable W)
    (hzero : ∀ τ, τ ≤ 0 → ∀ p, K τ p=0) (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ τ, 0 < τ → τ ≤ 1 → ∀ p, ‖K τ p‖^2 ≤ A*τ^(-(1/2 : ℝ))*‖W p‖^2) :
    (∫⁻ t, ∫⁻ s, ∫⁻ ω, ENNReal.ofReal (‖K ((t : ℝ)-(s : ℝ)) (s,ω)‖^2)
      ∂μ ∂timeMeasure H ∂timeMeasure H) ≤
      ENNReal.ofReal (2*A*(H : ℝ)^(1/2 : ℝ))*
        (∫⁻ s, ∫⁻ ω, ENNReal.ofReal (‖W (s,ω)‖^2) ∂μ ∂timeMeasure H) := by
  let f : ℝ≥0 → ℝ≥0∞ := fun s => ∫⁻ ω, ENNReal.ofReal (‖W (s,ω)‖^2) ∂μ
  have hf : Measurable f :=
    (ENNReal.continuous_ofReal.measurable.comp (hW.norm.pow_const 2)).lintegral_prod_right'
  have hb : (∫⁻ t, ∫⁻ s, ∫⁻ ω, ENNReal.ofReal (‖K ((t : ℝ)-(s : ℝ)) (s,ω)‖^2)
      ∂μ ∂timeMeasure H ∂timeMeasure H) ≤
      ∫⁻ t, ∫⁻ s, ENNReal.ofReal A*CompanionHeat.picardKernel H ((t : ℝ)-(s : ℝ))*f s
        ∂timeMeasure t ∂timeMeasure H := by
    apply lintegral_mono_ae
    filter_upwards [timeMeasure_ae_mem H] with t ht
    rw [CausalKernelInput.causal_integral K hzero μ ht.2]
    apply lintegral_mono_ae
    filter_upwards [timeMeasure_ae_mem t,(timeMeasure t).ae_ne t] with s hs hst
    have hst' : s < t := lt_of_le_of_ne hs.2 hst
    have hτ : 0 < (t : ℝ)-(s : ℝ) := sub_pos.mpr (by exact_mod_cast hst')
    have hτH : (t : ℝ)-(s : ℝ) ≤ H := by
      have htH : (t : ℝ) ≤ H := by exact_mod_cast ht.2
      linarith [s.2]
    have hk : CompanionHeat.picardKernel H ((t : ℝ)-(s : ℝ))=
        ENNReal.ofReal (((t : ℝ)-(s : ℝ))^(-(1/2 : ℝ))) :=
      Set.indicator_of_mem (show (t : ℝ)-(s : ℝ) ∈ Ioc (0 : ℝ) H from ⟨hτ,hτH⟩) _
    rw [hk,← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
    apply lintegral_mono
    intro ω
    dsimp only
    rw [← ENNReal.ofReal_mul hA,
      ← ENNReal.ofReal_mul (mul_nonneg hA (Real.rpow_nonneg hτ.le (-(1/2 : ℝ))))]
    exact ENNReal.ofReal_le_ofReal (hbound _ hτ (hτH.trans hH) (s,ω))
  calc
    _ ≤ _ := hb
    _ = ENNReal.ofReal A*(∫⁻ t, ∫⁻ s, CompanionHeat.picardKernel H ((t : ℝ)-(s : ℝ))*f s
        ∂timeMeasure t ∂timeMeasure H) := by
      simp_rw [mul_assoc,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal A*(ENNReal.ofReal (2*(H : ℝ)^(1/2 : ℝ))*(∫⁻ s, f s ∂timeMeasure H)) :=
      mul_le_mul_right (predictable_picard_causal_energy H f hf) _
    _ = _ := by
      rw [← mul_assoc,← ENNReal.ofReal_mul hA]
      congr 2
      ring

end SHEStochastic.CausalKernelComparison
