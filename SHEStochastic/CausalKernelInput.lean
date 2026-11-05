module

public import SHE.TimeCausalPowers
public import SHE.StandardTerminalIto

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.CausalKernelInput
open MeasureTheory Set SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω] [NormedAddCommGroup C]

theorem causal_integral (K : ℝ → (ℝ≥0 × Ω) → C)
    (hzero : ∀ τ, τ ≤ 0 → ∀ p, K τ p = 0) (μ : Measure Ω)
    {H t : ℝ≥0} (ht : t ≤ H) :
    (∫⁻ s, ∫⁻ ω, ENNReal.ofReal (‖K ((t : ℝ)-(s : ℝ)) (s,ω)‖ ^ 2) ∂μ ∂timeMeasure H) =
      ∫⁻ s, ∫⁻ ω, ENNReal.ofReal (‖K ((t : ℝ)-(s : ℝ)) (s,ω)‖ ^ 2) ∂μ ∂timeMeasure t := by
  rw [← timeMeasure_restrict ht, ← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr_ae
  filter_upwards [timeMeasure_ae_mem H] with s hs
  by_cases hst : s ≤ t
  · rw [Set.indicator_of_mem (show s ∈ Ioc 0 t from ⟨hs.1,hst⟩)]
  · rw [Set.indicator_of_notMem (show s ∉ Ioc 0 t from fun h => hst h.2)]
    have hτ : (t : ℝ)-(s : ℝ) ≤ 0 := sub_nonpos.mpr (by exact_mod_cast (le_of_not_ge hst))
    simp only [hzero _ hτ, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), ENNReal.ofReal_zero, lintegral_zero]

/-- A reusable fixed-time convolution energy estimate for every
causal Hilbert kernel with the integrable heat singularity. -/
theorem fixed_energy_upto (L : ℝ) (K : ℝ → (ℝ≥0 × Ω) → C)
    (hzero : ∀ τ, τ ≤ 0 → ∀ p, K τ p = 0) (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ τ, 0 < τ → τ ≤ L → ∀ p, ‖K τ p‖ ^ 2 ≤ A * τ ^ (-(1/2 : ℝ)))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {H t : ℝ≥0} (hH : (H : ℝ) ≤ L) (ht : t ≤ H) :
    (∫⁻ s, ∫⁻ ω, ENNReal.ofReal (‖K ((t : ℝ)-(s : ℝ)) (s,ω)‖ ^ 2) ∂μ ∂timeMeasure H) ≤
      ENNReal.ofReal (A * (2 * (t : ℝ) ^ (1/2 : ℝ))) := by
  rw [causal_integral K hzero μ ht]
  calc
    _ ≤ ∫⁻ s, ENNReal.ofReal A * ENNReal.ofReal (((t : ℝ)-(s : ℝ)) ^ (-(1/2 : ℝ))) ∂timeMeasure t := by
      apply lintegral_mono_ae
      filter_upwards [timeMeasure_ae_mem t] with s hs
      have hb (ω : Ω) : ‖K ((t : ℝ)-(s : ℝ)) (s,ω)‖ ^ 2 ≤
          A * ((t : ℝ)-(s : ℝ)) ^ (-(1/2 : ℝ)) := by
        rcases lt_or_eq_of_le hs.2 with hst | rfl
        · apply hbound _ (sub_pos.mpr (by exact_mod_cast hst))
          have hth : (t : ℝ) ≤ H := by exact_mod_cast ht
          linarith [s.2]
        · rw [sub_self, hzero _ le_rfl, norm_zero]
          simp
      have he := lintegral_mono (μ := μ) (fun ω => ENNReal.ofReal_le_ofReal (hb ω))
      rw [ENNReal.ofReal_mul hA] at he
      simpa only [lintegral_const, measure_univ, mul_one] using he
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        causal_rpow_mass (by norm_num : (-1 : ℝ) < -(1/2 : ℝ))]
      norm_num only [show -(1/2 : ℝ)+1=1/2 by norm_num]
      rw [← ENNReal.ofReal_mul hA]
      congr 1
      ring

theorem fixed_energy (K : ℝ → (ℝ≥0 × Ω) → C)
    (hzero : ∀ τ, τ ≤ 0 → ∀ p, K τ p = 0) (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ τ, 0 < τ → τ ≤ 1 → ∀ p, ‖K τ p‖ ^ 2 ≤ A * τ ^ (-(1/2 : ℝ)))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {H t : ℝ≥0} (hH : (H : ℝ) ≤ 1) (ht : t ≤ H) :
    (∫⁻ s, ∫⁻ ω, ENNReal.ofReal (‖K ((t : ℝ)-(s : ℝ)) (s,ω)‖ ^ 2) ∂μ ∂timeMeasure H) ≤
      ENNReal.ofReal (A * (2 * (t : ℝ) ^ (1/2 : ℝ))) :=
  fixed_energy_upto 1 K hzero A hA hbound μ hH ht

variable [MeasurableSpace C] [BorelSpace C]

/-- Predictability and the proved energy bound construct the actual
`L²` Itô input, uniformly for scalar, vector or derivative kernels. -/
theorem memLp_upto (L : ℝ) (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ℝ≥0) (hH : (H : ℝ) ≤ L) (K : ℝ → (ℝ≥0 × Ω) → C)
    (hzero : ∀ τ, τ ≤ 0 → ∀ p, K τ p = 0) (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ τ, 0 < τ → τ ≤ L → ∀ p, ‖K τ p‖ ^ 2 ≤ A * τ ^ (-(1/2 : ℝ)))
    (t : ℝ≥0) (ht : t ≤ H)
    (hp : StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω => K ((t : ℝ)-(p.1 : ℝ)) p)) :
    @MemLp _ _ F.predictable _ _ (fun p : ℝ≥0 × Ω => K ((t : ℝ)-(p.1 : ℝ)) p) 2
      ((energyMeasure μ H).trim (predictable_le_product F)) := by
  let f := fun p : ℝ≥0 × Ω => K ((t : ℝ)-(p.1 : ℝ)) p
  have ha := hp.mono (predictable_le_product F)
  have hm : Measurable (fun p => ENNReal.ofReal (‖f p‖ ^ 2)) :=
    ENNReal.continuous_ofReal.measurable.comp (ha.measurable.norm.pow_const 2)
  have hE : (∫⁻ p, ENNReal.ofReal (‖f p‖ ^ 2) ∂energyMeasure μ H) < ∞ := by
    change (∫⁻ p, ENNReal.ofReal (‖f p‖ ^ 2) ∂(timeMeasure H).prod μ) < ∞
    rw [lintegral_prod _ hm.aemeasurable]
    exact (fixed_energy_upto L K hzero A hA hbound μ hH ht).trans_lt ENNReal.ofReal_lt_top
  have hL : MemLp f 2 (energyMeasure μ H) := by
    apply (memLp_two_iff_integrable_sq_norm ha.aestronglyMeasurable).mpr
    exact ⟨(ha.norm.pow 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun p => sq_nonneg ‖f p‖))).mpr hE⟩
  change eLpNorm f 2 ((energyMeasure μ H).trim (predictable_le_product F)) < ∞
  rw [eLpNorm_trim (predictable_le_product F) hp]
  exact hL

theorem memLp (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ℝ≥0) (hH : (H : ℝ) ≤ 1) (K : ℝ → (ℝ≥0 × Ω) → C)
    (hzero : ∀ τ, τ ≤ 0 → ∀ p, K τ p = 0) (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ τ, 0 < τ → τ ≤ 1 → ∀ p, ‖K τ p‖ ^ 2 ≤ A * τ ^ (-(1/2 : ℝ)))
    (t : ℝ≥0) (ht : t ≤ H)
    (hp : StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω => K ((t : ℝ)-(p.1 : ℝ)) p)) :
    @MemLp _ _ F.predictable _ _ (fun p : ℝ≥0 × Ω => K ((t : ℝ)-(p.1 : ℝ)) p) 2
      ((energyMeasure μ H).trim (predictable_le_product F)) :=
  memLp_upto 1 F μ H hH K hzero A hA hbound t ht hp

end SHEStochastic.CausalKernelInput
