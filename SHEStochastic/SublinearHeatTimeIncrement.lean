module

public import SHEStochastic.SublinearHeatCoefficientEnergy
public import SHEStochastic.HeatIncrementWeightedRate
public import SHE.HeatTimeSmoothing

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.SublinearHeatTimeIncrement
open MeasureTheory SHE SHE.StoppedFourier SHE.NativeHeatSpan AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The existing unit-circle semigroup increment estimate transports
isometrically to the physical circle, with the clock ratio cancelling. -/
theorem operator_bound {t δ θ : ℝ} (ht : 0 < t) (hδ : 0 ≤ δ)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (v : CircleL2) :
    ‖circleHeatOperator δ hδ (circleHeatOperator t ht.le v) - circleHeatOperator t ht.le v‖ ≤
      (δ / t) ^ θ * ‖v‖ := by
  let w := CircleNormalization.push.symm v
  have he (r : ℝ) (hr : 0 ≤ r) (z : CircleHeat.CircleL2) :
      CircleNormalization.push (CircleHeat.heat (clock r) z) =
        circleHeatOperator r hr (CircleNormalization.push z) := by
    have hh := CircleNormalization.push_heat (clock r) (div_nonneg hr (by positivity)) z
    have hc : (2 * Real.pi) ^ 2 * clock r = r := by unfold clock; field_simp; ring
    simpa only [hc] using hh
  have hratio : clock δ / clock t = δ / t := by
    unfold clock
    field_simp
  have hh := HeatTimeSmoothing.heat_increment_bound (τ := clock t) (δ := clock δ) (clock_pos ht)
    (div_nonneg hδ (by positivity)) hθ hθ1 w
  rw [hratio] at hh
  calc
    _ = ‖CircleNormalization.push
        (CircleHeat.heat (clock δ) (CircleHeat.heat (clock t) w) - CircleHeat.heat (clock t) w)‖ := by
      rw [map_sub, he δ hδ, he t ht.le, LinearIsometryEquiv.apply_symm_apply]
    _ ≤ (δ / t) ^ θ * ‖w‖ := by rwa [LinearIsometryEquiv.norm_map]
    _ = _ := by rw [LinearIsometryEquiv.norm_map]

theorem kernel_l2_bound {t δ θ : ℝ} (ht : 0 < t) (hδ : 0 ≤ δ)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (a : HeatCircle) :
    ‖circleHeat (t + δ) a - circleHeat t a‖ ≤
      (δ / (t / 2)) ^ θ * ‖circleHeat (t / 2) a‖ := by
  have hhalf : 0 < t / 2 := by positivity
  have he : circleHeatOperator (t / 2) hhalf.le (circleHeat (t / 2) a) = circleHeat t a := by
    simpa only [show t / 2 + t / 2 = t by ring] using circleHeatOperator_heat hhalf.le hhalf a
  have hh := operator_bound hhalf hδ hθ hθ1 (circleHeat (t / 2) a)
  rw [he, circleHeatOperator_heat hδ ht, add_comm δ t] at hh
  exact hh

/-- The squared spatial integral of the continuous kernel difference is
the actual Hilbert norm, not an assumed kernel-energy formula. -/
theorem difference_energy {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (a : HeatCircle) :
    (∫⁻ x, ENNReal.ofReal (‖kernel s hs a x - kernel t ht a x‖ ^ 2) ∂haarAddCircle) =
      ENNReal.ofReal (‖circleHeat s a - circleHeat t a‖ ^ 2) := by
  let v := circleHeat s a - circleHeat t a
  have hae : (v : HeatCircle → ℂ) =ᵐ[haarAddCircle]
      fun x ↦ kernel s hs a x - kernel t ht a x := by
    filter_upwards [Lp.coeFn_sub (circleHeat s a) (circleHeat t a), kernel_physical_ae hs a,
      kernel_physical_ae ht a, ProfileVariance.heatPhysical_ae hs a,
      ProfileVariance.heatPhysical_ae ht a] with x hv hks hkt hps hpt
    exact hv.trans (by rw [hks, hkt, hps, hpt]; rfl)
  rw [L2_norm_sq_eq_integral]
  rw [ofReal_integral_eq_lintegral_ofReal (Lp.memLp v).norm.integrable_sq
    (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)]
  exact lintegral_congr_ae (hae.mono fun _ hx ↦ by rw [hx]) |>.symm

theorem energy_bound {t δ θ : ℝ} (ht : 0 < t) (hδ : 0 ≤ δ)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (a : HeatCircle) :
    (∫⁻ x, ENNReal.ofReal
      (‖kernel (t + δ) (add_pos_of_pos_of_nonneg ht hδ) a x - kernel t ht a x‖ ^ 2) ∂haarAddCircle) ≤
      ENNReal.ofReal (((δ / (t / 2)) ^ θ) ^ 2 *
        (1 + heatConstant * (t / 2) ^ (-(1 / 2 : ℝ)))) := by
  rw [difference_energy]
  apply ENNReal.ofReal_le_ofReal
  have hh := pow_le_pow_left₀ (norm_nonneg _) (kernel_l2_bound ht hδ hθ hθ1 a) 2
  rw [mul_pow] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (circleHeat_norm_sq_bound (by positivity : 0 < t / 2) a) (sq_nonneg _))

def smallTimeConstant : ℝ :=
  1 + 2 ^ (1 / 4 : ℝ) * ScaledHeatTraceEnvelope.constant 1 2

theorem constant_ge_one : 1 ≤ smallTimeConstant := by
  have hc := ScaledHeatTraceEnvelope.constant_nonneg (M := 1) (scale := 2) (by norm_num) (by norm_num)
  unfold smallTimeConstant
  exact le_add_of_nonneg_right (mul_nonneg (by positivity) hc)

theorem cap_rate {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    SublinearHeatRows.cap t ≤ smallTimeConstant * t ^ (-(1 / 2 : ℝ)) := by
  have hc := ScaledHeatTraceEnvelope.constant_nonneg (M := 1) (scale := 2) (by norm_num) (by norm_num)
  have h2 := Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hh : ScaledHeatTraceEnvelope.constant 1 2 ≤ smallTimeConstant := by
    unfold smallTimeConstant
    nlinarith
  exact (SublinearHeatRows.cap_bound ht ht1).trans (mul_le_mul_of_nonneg_right hh (by positivity))

theorem energy_rate {t δ : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hδ : 0 ≤ δ) (a : HeatCircle) :
    (∫⁻ x, ENNReal.ofReal
      (‖kernel (t + δ) (add_pos_of_pos_of_nonneg ht hδ) a x - kernel t ht a x‖ ^ 2) ∂haarAddCircle) ≤
      ENNReal.ofReal (smallTimeConstant * δ ^ (1 / 4 : ℝ) * t ^ (-(3 / 4 : ℝ))) := by
  apply (energy_bound ht hδ (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num) a).trans
  apply ENNReal.ofReal_le_ofReal
  change ((δ / (t / 2)) ^ (1 / 8 : ℝ)) ^ 2 * SublinearHeatRows.cap t ≤ _
  calc
    _ ≤ ((δ / (t / 2)) ^ (1 / 8 : ℝ)) ^ 2 *
        (ScaledHeatTraceEnvelope.constant 1 2 * t ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left (SublinearHeatRows.cap_bound ht ht1) (sq_nonneg _)
    _ = (2 ^ (1 / 4 : ℝ) * ScaledHeatTraceEnvelope.constant 1 2) *
        δ ^ (1 / 4 : ℝ) * t ^ (-(3 / 4 : ℝ)) := HeatIncrementRateAlgebra.time_ratio ht hδ
    _ ≤ _ := by
      gcongr
      exact le_add_of_nonneg_left zero_le_one

/-- The actual coefficient-weighted time difference has a positive
increment exponent (1-β)/4 and integrable age exponent (3+β)/4.
The only state factor is its L² norm; G need not be bounded. -/
theorem holder_rate {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup V] {G : E → V} {C β : ℝ≥0}
    (hG : HolderWith C β G) (hβ1 : β ≤ 1)
    (u : Lp E 2 (haarAddCircle (T := 2 * Real.pi))) {t δ : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (a : HeatCircle) :
    (∫⁻ x, ENNReal.ofReal
      (‖kernel (t + δ) (add_pos_of_pos_of_nonneg ht hδ) a x - kernel t ht a x‖ ^ 2 *
        ‖G (u x)‖ ^ 2) ∂haarAddCircle) ≤
      ENNReal.ofReal (2 * (‖G 0‖ + (C : ℝ)) ^ 2 * 4 ^ (β : ℝ) * smallTimeConstant ^ (1 + (β : ℝ)) *
        δ ^ ((1 - (β : ℝ)) / 4) * t ^ (-(3 + (β : ℝ)) / 4)) *
          (1 + ENNReal.ofReal (‖u‖ ^ 2) ^ (β : ℝ)) := by
  let h (x : HeatCircle) := ENNReal.ofReal
    (‖kernel (t + δ) (add_pos_of_pos_of_nonneg ht hδ) a x - kernel t ht a x‖ ^ 2)
  have hh : Measurable h :=
    (((kernel (t + δ) (add_pos_of_pos_of_nonneg ht hδ) a).continuous.sub
      (kernel t ht a).continuous).norm.pow 2).measurable.ennreal_ofReal
  have hb : ∀ᵐ x ∂haarAddCircle, h x ≤
      ENNReal.ofReal (4 * (smallTimeConstant * t ^ (-(1 / 2 : ℝ))) ^ 2) := by
    filter_upwards [SublinearHeatRows.kernel_bound ht a,
      SublinearHeatRows.kernel_bound (add_pos_of_pos_of_nonneg ht hδ) a] with x hx hy
    have hc := SublinearHeatRows.cap_antitone ht (le_add_of_nonneg_right hδ)
    have hd : ‖kernel (t + δ) (add_pos_of_pos_of_nonneg ht hδ) a x - kernel t ht a x‖ ≤
        2 * (smallTimeConstant * t ^ (-(1 / 2 : ℝ))) :=
      (norm_sub_le _ _).trans (by linarith [cap_rate ht ht1])
    have hs := pow_le_pow_left₀ (norm_nonneg _) hd 2
    exact ENNReal.ofReal_le_ofReal (hs.trans_eq (by ring))
  have ht := HeatIncrementWeightedRate.bound hG hβ1 u h hh.aemeasurable
    constant_ge_one ht ht1 hδ hδ1 hb (energy_rate ht ht1 hδ a)
  simpa only [h, ENNReal.ofReal_mul (sq_nonneg _)] using ht

theorem causal_mass {β : ℝ} (hβ : β < 1) (T : ℝ≥0) :
    (∫⁻ s, ENNReal.ofReal (((T : ℝ) - (s : ℝ)) ^ (-(3 + β) / 4)) ∂PredictableL2.timeMeasure T) =
      ENNReal.ofReal ((T : ℝ) ^ ((1 - β) / 4) / ((1 - β) / 4)) := by
  have hh := PredictableL2.causal_rpow_mass (α := -(3 + β) / 4) (by linarith) T
  simpa only [show -(3 + β) / 4 + 1 = (1 - β) / 4 by ring] using hh

end SHEStochastic.SublinearHeatTimeIncrement
