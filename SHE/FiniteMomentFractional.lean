module

public import SHE.FractionalMoment

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.FiniteMomentFractional
open MeasureTheory
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem lintegral_fraction_mass {F : Ω → ℝ≥0∞} (hF : AEMeasurable F μ)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    (∫⁻ ω, F ω ^ β ∂μ) ≤ (∫⁻ ω, F ω ∂μ) ^ β * (μ Set.univ) ^ (1 - β) := by
  have hh := ENNReal.lintegral_mul_norm_pow_le hF
    (aemeasurable_const : AEMeasurable (fun _ : Ω => (1 : ℝ≥0∞)) μ)
    hβ (sub_nonneg.mpr hβ1) (by ring : β + (1 - β) = 1)
  simpa only [ENNReal.one_rpow, mul_one, lintegral_const, one_mul] using hh

/-- The exact event-mass form of Lyapunov. It preserves a conditional
moment bound after restricting to any initial event, including null events. -/
theorem moment_fraction_mass {Y : Ω → ℝ} (hY : AEStronglyMeasurable Y μ)
    {q β C : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hC : 0 ≤ C)
    (hb : (∫⁻ ω, ENNReal.ofReal (‖Y ω‖ ^ q) ∂μ) ≤ ENNReal.ofReal C * μ Set.univ) :
    (∫⁻ ω, ENNReal.ofReal (‖Y ω‖ ^ (q * β)) ∂μ) ≤
      ENNReal.ofReal (C ^ β) * μ Set.univ := by
  have hm : AEMeasurable (fun ω => ENNReal.ofReal (‖Y ω‖ ^ q)) μ :=
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable (hY.norm.aemeasurable.pow_const q)
  have he (ω : Ω) : ENNReal.ofReal (‖Y ω‖ ^ (q * β)) = ENNReal.ofReal (‖Y ω‖ ^ q) ^ β := by
    rw [Real.rpow_mul (norm_nonneg _), ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hβ]
  simp_rw [he]
  calc
    _ ≤ (∫⁻ ω, ENNReal.ofReal (‖Y ω‖ ^ q) ∂μ) ^ β * (μ Set.univ) ^ (1 - β) :=
      lintegral_fraction_mass hm hβ hβ1
    _ ≤ (ENNReal.ofReal C * μ Set.univ) ^ β * (μ Set.univ) ^ (1 - β) :=
      mul_le_mul_left (ENNReal.rpow_le_rpow hb hβ) _
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hβ, mul_assoc,
        ← ENNReal.rpow_add_of_nonneg β (1 - β) hβ (sub_nonneg.mpr hβ1),
        show β + (1 - β) = (1 : ℝ) by ring, ENNReal.rpow_one,
        ENNReal.ofReal_rpow_of_nonneg hC hβ]

end SHE.FiniteMomentFractional
