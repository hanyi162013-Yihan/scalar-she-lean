module

public import SHEStochastic.WeightedSublinearEnergy
public import SHE.NativeHeatKernel
public import SHE.ProfileL2
public import SHE.ScaledHeatTraceEnvelope
public import SHE.TimeCausalPowers

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.SublinearHeatRows
open MeasureTheory SHE SHE.StoppedFourier SHE.ProfileVariance AddCircle Set
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

def cap (t : ℝ) : ℝ := 1 + heatConstant * (t / 2) ^ (-(1 / 2 : ℝ))

theorem cap_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ cap t := by
  have hC := heatConstant_pos
  unfold cap
  positivity

theorem cap_antitone {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) : cap t ≤ cap s := by
  have hh := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < s / 2)
    (div_le_div_of_nonneg_right hst (by norm_num : (0 : ℝ) ≤ 2)) (by norm_num : -(1 / 2 : ℝ) ≤ 0)
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hh heatConstant_pos.le)

theorem cap_power_bound {t β : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hβ : 0 ≤ β) :
    cap t ^ (1 + β) ≤ ScaledHeatTraceEnvelope.constant 1 2 ^ (1 + β) *
      t ^ (-(1 + β) / 2) := by
  have hc : 0 ≤ ScaledHeatTraceEnvelope.constant 1 2 :=
    ScaledHeatTraceEnvelope.constant_nonneg (by norm_num) (by norm_num)
  have hb : cap t ≤ ScaledHeatTraceEnvelope.constant 1 2 * t ^ (-(1 / 2 : ℝ)) := by
    simpa only [cap, heatConstant, one_mul] using
      ScaledHeatTraceEnvelope.scalar_bound (M := 1) (scale := 2)
        (by norm_num) (by norm_num) ht ht1
  have hh := Real.rpow_le_rpow (cap_nonneg ht.le) hb (by linarith : 0 ≤ 1 + β)
  rw [Real.mul_rpow hc (Real.rpow_nonneg ht.le _), ← Real.rpow_mul ht.le] at hh
  convert hh using 1
  congr 2
  ring

theorem cap_bound {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    cap t ≤ ScaledHeatTraceEnvelope.constant 1 2 * t ^ (-(1 / 2 : ℝ)) := by
  simpa only [add_zero, Real.rpow_one, show -(1 : ℝ) / 2 = -(1 / 2 : ℝ) by ring] using
    cap_power_bound (β := 0) ht ht1 le_rfl

/-- The unbounded-coefficient time singularity is integrable exactly
when β<1. The actual native time measure and endpoint are retained. -/
theorem causal_mass {β : ℝ} (hβ : β < 1) (T : ℝ≥0) :
    (∫⁻ s, ENNReal.ofReal (((T : ℝ) - (s : ℝ)) ^ (-(1 + β) / 2)) ∂PredictableL2.timeMeasure T) =
      ENNReal.ofReal ((T : ℝ) ^ ((1 - β) / 2) / ((1 - β) / 2)) := by
  have hh := PredictableL2.causal_rpow_mass (α := -(1 + β) / 2) (by linarith) T
  simpa only [show -(1 + β) / 2 + 1 = (1 - β) / 2 by ring] using hh

/-- The exact continuous native heat kernel has the required uniform
cap. Both the cap and normalization are derived from existing heat lemmas. -/
theorem kernel_bound {t : ℝ} (ht : 0 < t) (a : HeatCircle) :
    ∀ᵐ x ∂haarAddCircle, ‖NativeHeatSpan.kernel t ht a x‖ ≤ cap t := by
  filter_upwards [NativeHeatSpan.kernel_physical_ae ht a] with x hx
  rw [hx]
  have hh := ProfileL2.heatPhysical_square_uniform_bound ht a x
  have hc := circleHeat_norm_sq_bound (by positivity : 0 < t / 2) (0 : HeatCircle)
  have hb : ‖heatPhysical t a x‖ ≤ ‖circleHeat (t / 2) (0 : HeatCircle)‖ ^ 2 := by
    nlinarith [norm_nonneg (heatPhysical t a x), sq_nonneg ‖circleHeat (t / 2) (0 : HeatCircle)‖]
  exact hb.trans hc

def density {t : ℝ} (ht : 0 < t) (a : HeatCircle) (x : HeatCircle) : ℝ≥0∞ :=
  ENNReal.ofReal ‖NativeHeatSpan.kernel t ht a x‖

theorem density_properties {t : ℝ} (ht : 0 < t) (a : HeatCircle) :
    Measurable (density ht a) ∧ (∫⁻ x, density ht a x ∂haarAddCircle) = 1 ∧
      ∀ᵐ x ∂haarAddCircle, density ht a x ≤ ENNReal.ofReal (cap t) := by
  refine ⟨(NativeHeatSpan.kernel t ht a).continuous.norm.measurable.ennreal_ofReal, ?_,
    (kernel_bound ht a).mono fun _ hx ↦ ENNReal.ofReal_le_ofReal hx⟩
  have hi : Integrable (fun x : HeatCircle ↦ ‖NativeHeatSpan.kernel t ht a x‖) haarAddCircle := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      (NativeHeatSpan.kernel t ht a).continuous.norm.continuousOn.integrableOn_compact (K := univ) isCompact_univ
  change (∫⁻ x, ENNReal.ofReal ‖NativeHeatSpan.kernel t ht a x‖ ∂haarAddCircle) = 1
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _), NativeHeatSpan.kernel_norm_mass ht a]
  exact ENNReal.ofReal_one

/-- The actual heat kernel, with a sublinear spatial input. For
f=|v|², the last factor is the L²-state energy to the power β. -/
theorem weighted_bound {t : ℝ} (ht : 0 < t) (a : HeatCircle)
    (f : HeatCircle → ℝ≥0∞) (hf : AEMeasurable f haarAddCircle)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    (∫⁻ x, ENNReal.ofReal (‖NativeHeatSpan.kernel t ht a x‖ ^ 2) * f x ^ β ∂haarAddCircle) ≤
      ENNReal.ofReal (cap t) ^ (1 + β) * (∫⁻ x, f x ∂haarAddCircle) ^ β := by
  obtain ⟨hk, hm, hb⟩ := density_properties ht a
  have hh := WeightedSublinearEnergy.kernel_power haarAddCircle (density ht a) f hk.aemeasurable hf
    (ENNReal.ofReal (cap t)) hb hm hβ hβ1
  simpa only [density, ENNReal.ofReal_pow (norm_nonneg _) 2] using hh

theorem square_mass_bound {t : ℝ} (ht : 0 < t) (a : HeatCircle) :
    (∫⁻ x, ENNReal.ofReal (‖NativeHeatSpan.kernel t ht a x‖ ^ 2) ∂haarAddCircle) ≤
      ENNReal.ofReal (cap t) := by
  simpa only [ENNReal.rpow_zero, mul_one, add_zero, ENNReal.rpow_one] using
    weighted_bound ht a (fun _ ↦ 1) aemeasurable_const (β := 0) le_rfl zero_le_one

end SHEStochastic.SublinearHeatRows
