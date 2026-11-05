module

public import SHEStochastic.SublinearHeatCoefficientEnergy
public import SHEStochastic.HeatIncrementWeightedRate
public import SHE.HeatKernelLocal

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.SublinearHeatSpatialIncrement
open MeasureTheory SHE SHE.StoppedFourier SHE.NativeHeatSpan AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Local spatial differences of the actual native kernel are bounded
by a dilated positive kernel. The unit-circle distance keeps every
normalization explicit and reuses the existing periodization estimate. -/
theorem local_bound {t : ℝ} (ht : 0 < t) (a b x : HeatCircle)
    (hab : ‖unitCenter a - unitCenter b‖ ≤ Real.sqrt (clock t)) :
    ‖kernel t ht a x - kernel t ht b x‖ ≤
      (HeatMarkov.localConstant / Real.sqrt (clock t) * ‖unitCenter a - unitCenter b‖) *
        ‖kernel (8 * t) (by positivity) a x‖ := by
  have hh := HeatMarkov.kernel_translation_bound (clock_pos ht)
    (unitCenter x - unitCenter a) (unitCenter a - unitCenter b) hab
  have he : 8 * clock t = clock (8 * t) := by unfold clock; ring
  simp only [show (unitCenter x - unitCenter a) + (unitCenter a - unitCenter b) =
    unitCenter x - unitCenter b by abel, he] at hh
  change ‖kernel t ht a x - kernel t ht b x‖ ≤
    (HeatMarkov.localConstant / Real.sqrt (clock t)) * ‖kernel (8 * t) (by positivity) a x‖ *
      ‖unitCenter a - unitCenter b‖ at hh
  exact hh.trans_eq (by ring)

/-- The local difference energy estimate allows any coefficient weight.
In particular, no uniform bound on G is required to use this step. -/
theorem weighted_local {t : ℝ} (ht : 0 < t) (a b : HeatCircle)
    (hab : ‖unitCenter a - unitCenter b‖ ≤ Real.sqrt (clock t)) (g : HeatCircle → ℝ≥0∞) :
    (∫⁻ x, ENNReal.ofReal (‖kernel t ht a x - kernel t ht b x‖ ^ 2) * g x ∂haarAddCircle) ≤
      ENNReal.ofReal ((HeatMarkov.localConstant / Real.sqrt (clock t) *
        ‖unitCenter a - unitCenter b‖) ^ 2) *
          ∫⁻ x, ENNReal.ofReal (‖kernel (8 * t) (by positivity) a x‖ ^ 2) * g x ∂haarAddCircle := by
  let c := HeatMarkov.localConstant / Real.sqrt (clock t) * ‖unitCenter a - unitCenter b‖
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (c ^ 2) *
        (ENNReal.ofReal (‖kernel (8 * t) (by positivity) a x‖ ^ 2) * g x) ∂haarAddCircle := by
      apply lintegral_mono
      intro x
      have hh := pow_le_pow_left₀ (norm_nonneg _) (local_bound ht a b x hab) 2
      rw [mul_pow] at hh
      have he := ENNReal.ofReal_le_ofReal hh
      rw [ENNReal.ofReal_mul (sq_nonneg c)] at he
      exact (mul_le_mul_left he (g x)).trans_eq (mul_assoc _ _ _)
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem energy_local {t : ℝ} (ht : 0 < t) (a b : HeatCircle)
    (hab : ‖unitCenter a - unitCenter b‖ ≤ Real.sqrt (clock t)) :
    (∫⁻ x, ENNReal.ofReal (‖kernel t ht a x - kernel t ht b x‖ ^ 2) ∂haarAddCircle) ≤
      ENNReal.ofReal ((HeatMarkov.localConstant / Real.sqrt (clock t) *
        ‖unitCenter a - unitCenter b‖) ^ 2 * SublinearHeatRows.cap t) := by
  have hh := weighted_local ht a b hab (fun _ ↦ 1)
  simp only [mul_one] at hh
  have hm := (SublinearHeatRows.square_mass_bound (by positivity : 0 < 8 * t) a).trans
    (ENNReal.ofReal_le_ofReal (SublinearHeatRows.cap_antitone ht (by linarith)))
  apply hh.trans
  rw [ENNReal.ofReal_mul (sq_nonneg _)]
  exact mul_le_mul_right hm _

theorem energy_bound {t : ℝ} (ht : 0 < t) (a b : HeatCircle) :
    (∫⁻ x, ENNReal.ofReal (‖kernel t ht a x - kernel t ht b x‖ ^ 2) ∂haarAddCircle) ≤
      ENNReal.ofReal (4 * SublinearHeatRows.cap t) := by
  let f (x : HeatCircle) := ENNReal.ofReal (‖kernel t ht a x‖ ^ 2)
  let g (x : HeatCircle) := ENNReal.ofReal (‖kernel t ht b x‖ ^ 2)
  have hf : Measurable f := ((kernel t ht a).continuous.norm.pow 2).measurable.ennreal_ofReal
  have hg : Measurable g := ((kernel t ht b).continuous.norm.pow 2).measurable.ennreal_ofReal
  calc
    _ ≤ ∫⁻ x, (2 : ℝ≥0∞) * (f x + g x) ∂haarAddCircle := by
      apply lintegral_mono
      intro x
      have hs := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (kernel t ht a x) (kernel t ht b x)) 2
      have hr : ‖kernel t ht a x - kernel t ht b x‖ ^ 2 ≤
          2 * (‖kernel t ht a x‖ ^ 2 + ‖kernel t ht b x‖ ^ 2) := by
        nlinarith [sq_nonneg (‖kernel t ht a x‖ - ‖kernel t ht b x‖)]
      apply (ENNReal.ofReal_le_ofReal hr).trans_eq
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
        ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    _ = 2 * ((∫⁻ x, f x ∂haarAddCircle) + ∫⁻ x, g x ∂haarAddCircle) := by
      rw [lintegral_const_mul'' 2 (f := fun x ↦ f x + g x) (hf.add hg).aemeasurable,
        lintegral_add_left' hf.aemeasurable]
    _ ≤ 2 * (ENNReal.ofReal (SublinearHeatRows.cap t) + ENNReal.ofReal (SublinearHeatRows.cap t)) :=
      mul_le_mul_right (add_le_add (SublinearHeatRows.square_mass_bound ht a)
        (SublinearHeatRows.square_mass_bound ht b)) _
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num; ring

/-- Local derivative control and the global energy bound interpolate
without differentiating the coefficient or requiring bounded states. -/
theorem energy_fractional {t : ℝ} (ht : 0 < t) (a b : HeatCircle) :
    (∫⁻ x, ENNReal.ofReal (‖kernel t ht a x - kernel t ht b x‖ ^ 2) ∂haarAddCircle) ≤
      ENNReal.ofReal ((HeatMarkov.localConstant ^ 2 + 4) * SublinearHeatRows.cap t *
        (‖unitCenter a - unitCenter b‖ / Real.sqrt (clock t)) ^ (1 / 2 : ℝ)) := by
  let d := ‖unitCenter a - unitCenter b‖
  let r := d / Real.sqrt (clock t)
  let B := HeatMarkov.localConstant ^ 2 + 4
  have hd : 0 ≤ d := norm_nonneg _
  have hs : 0 < Real.sqrt (clock t) := Real.sqrt_pos.mpr (clock_pos ht)
  have hr : 0 ≤ r := div_nonneg hd hs.le
  have hcap := SublinearHeatRows.cap_nonneg ht.le
  have hB : HeatMarkov.localConstant ^ 2 ≤ B := by dsimp [B]; linarith
  by_cases hnear : d ≤ Real.sqrt (clock t)
  · have hr1 : r ≤ 1 := (div_le_one hs).mpr hnear
    have hp : r ^ 2 ≤ r ^ (1 / 2 : ℝ) := by
      simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge' hr hr1
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 2)
    have he : (HeatMarkov.localConstant / Real.sqrt (clock t) * d) ^ 2 * SublinearHeatRows.cap t =
        (HeatMarkov.localConstant ^ 2 * r ^ 2) * SublinearHeatRows.cap t := by dsimp [r]; ring
    calc
      _ ≤ ENNReal.ofReal ((HeatMarkov.localConstant / Real.sqrt (clock t) * d) ^ 2 *
          SublinearHeatRows.cap t) := energy_local ht a b hnear
      _ = ENNReal.ofReal ((HeatMarkov.localConstant ^ 2 * r ^ 2) * SublinearHeatRows.cap t) :=
        congrArg ENNReal.ofReal he
      _ ≤ ENNReal.ofReal ((B * r ^ (1 / 2 : ℝ)) * SublinearHeatRows.cap t) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
          (mul_le_mul hB hp (sq_nonneg _) (by dsimp [B]; positivity)) hcap)
      _ = _ := congrArg ENNReal.ofReal (by ring)
  · have hr1 : 1 ≤ r := (one_le_div hs).mpr (le_of_not_ge hnear)
    have hp := Real.one_le_rpow hr1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hb : 4 ≤ B * r ^ (1 / 2 : ℝ) := by
      dsimp [B]
      nlinarith [sq_nonneg HeatMarkov.localConstant]
    exact (energy_bound ht a b).trans (ENNReal.ofReal_le_ofReal
      ((mul_le_mul_of_nonneg_right hb hcap).trans_eq (by ring)))

def smallTimeConstant : ℝ := 1 + ScaledHeatTraceEnvelope.constant 1 2 +
  (HeatMarkov.localConstant ^ 2 + 4) * (4 * Real.pi ^ 2) ^ (1 / 4 : ℝ) *
    ScaledHeatTraceEnvelope.constant 1 2

theorem constant_bounds : 1 ≤ smallTimeConstant ∧
    ScaledHeatTraceEnvelope.constant 1 2 ≤ smallTimeConstant ∧
      (HeatMarkov.localConstant ^ 2 + 4) * (4 * Real.pi ^ 2) ^ (1 / 4 : ℝ) *
        ScaledHeatTraceEnvelope.constant 1 2 ≤ smallTimeConstant := by
  have hc := ScaledHeatTraceEnvelope.constant_nonneg (M := 1) (scale := 2) (by norm_num) (by norm_num)
  have hp : 0 ≤ (HeatMarkov.localConstant ^ 2 + 4) * (4 * Real.pi ^ 2) ^ (1 / 4 : ℝ) *
      ScaledHeatTraceEnvelope.constant 1 2 := by positivity
  unfold smallTimeConstant
  exact ⟨by linarith, by linarith, by linarith⟩

theorem cap_rate {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    SublinearHeatRows.cap t ≤ smallTimeConstant * t ^ (-(1 / 2 : ℝ)) :=
  (SublinearHeatRows.cap_bound ht ht1).trans (mul_le_mul_of_nonneg_right constant_bounds.2.1 (by positivity))

theorem energy_rate {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (a b : HeatCircle) :
    (∫⁻ x, ENNReal.ofReal (‖kernel t ht a x - kernel t ht b x‖ ^ 2) ∂haarAddCircle) ≤
      ENNReal.ofReal (smallTimeConstant * (‖unitCenter a - unitCenter b‖ ^ 2) ^ (1 / 4 : ℝ) *
        t ^ (-(3 / 4 : ℝ))) := by
  apply (energy_fractional ht a b).trans
  apply ENNReal.ofReal_le_ofReal
  let d := ‖unitCenter a - unitCenter b‖
  let B := HeatMarkov.localConstant ^ 2 + 4
  have hd : 0 ≤ d := norm_nonneg _
  have he : d ^ (1 / 2 : ℝ) = (d ^ 2) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_natCast_mul hd 2 (1 / 4 : ℝ)]
    norm_num
  calc
    _ ≤ B * (ScaledHeatTraceEnvelope.constant 1 2 * t ^ (-(1 / 2 : ℝ))) *
        (d / Real.sqrt (clock t)) ^ (1 / 2 : ℝ) := by
      gcongr
      exact SublinearHeatRows.cap_bound ht ht1
    _ = B * ((d / Real.sqrt (clock t)) ^ (1 / 2 : ℝ) *
        (ScaledHeatTraceEnvelope.constant 1 2 * t ^ (-(1 / 2 : ℝ)))) := by ring
    _ = B * (((4 * Real.pi ^ 2) ^ (1 / 4 : ℝ) * ScaledHeatTraceEnvelope.constant 1 2) *
        d ^ (1 / 2 : ℝ) * t ^ (-(3 / 4 : ℝ))) := by
      rw [clock, HeatIncrementRateAlgebra.space_ratio (by positivity : 0 < 4 * Real.pi ^ 2) ht hd]
    _ = (B * (4 * Real.pi ^ 2) ^ (1 / 4 : ℝ) * ScaledHeatTraceEnvelope.constant 1 2) *
        d ^ (1 / 2 : ℝ) * t ^ (-(3 / 4 : ℝ)) := by ring
    _ ≤ smallTimeConstant * d ^ (1 / 2 : ℝ) * t ^ (-(3 / 4 : ℝ)) := by
      gcongr
      exact constant_bounds.2.2
    _ = _ := by rw [he]

/-- Spatial increments of the actual unbounded-coefficient heat row.
The same interpolation theorem as for time increments supplies the
coefficient step, for scalar and finite matrix output alike. -/
theorem holder_rate {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup V] {G : E → V} {C β : ℝ≥0}
    (hG : HolderWith C β G) (hβ1 : β ≤ 1)
    (u : Lp E 2 (haarAddCircle (T := 2 * Real.pi))) {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (a b : HeatCircle) :
    (∫⁻ x, ENNReal.ofReal (‖kernel t ht a x - kernel t ht b x‖ ^ 2 * ‖G (u x)‖ ^ 2) ∂haarAddCircle) ≤
      ENNReal.ofReal (2 * (‖G 0‖ + (C : ℝ)) ^ 2 * 4 ^ (β : ℝ) * smallTimeConstant ^ (1 + (β : ℝ)) *
        (‖unitCenter a - unitCenter b‖ ^ 2) ^ ((1 - (β : ℝ)) / 4) * t ^ (-(3 + (β : ℝ)) / 4)) *
          (1 + ENNReal.ofReal (‖u‖ ^ 2) ^ (β : ℝ)) := by
  let h (x : HeatCircle) := ENNReal.ofReal (‖kernel t ht a x - kernel t ht b x‖ ^ 2)
  have hh : Measurable h := (((kernel t ht a).continuous.sub (kernel t ht b).continuous).norm.pow 2).measurable.ennreal_ofReal
  have hb : ∀ᵐ x ∂haarAddCircle, h x ≤
      ENNReal.ofReal (4 * (smallTimeConstant * t ^ (-(1 / 2 : ℝ))) ^ 2) := by
    filter_upwards [SublinearHeatRows.kernel_bound ht a, SublinearHeatRows.kernel_bound ht b] with x hx hy
    have hd : ‖kernel t ht a x - kernel t ht b x‖ ≤ 2 * (smallTimeConstant * t ^ (-(1 / 2 : ℝ))) :=
      (norm_sub_le _ _).trans (by linarith [cap_rate ht ht1])
    exact ENNReal.ofReal_le_ofReal ((pow_le_pow_left₀ (norm_nonneg _) hd 2).trans_eq (by ring))
  have hdist : ‖unitCenter a - unitCenter b‖ ≤ (1 / 2 : ℝ) := by
    simpa only [abs_one] using AddCircle.norm_le_half_period (p := 1) (x := unitCenter a - unitCenter b) (by norm_num)
  have hd1 : ‖unitCenter a - unitCenter b‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (unitCenter a - unitCenter b)]
  have ht := HeatIncrementWeightedRate.bound hG hβ1 u h hh.aemeasurable constant_bounds.1 ht ht1
    (sq_nonneg _) hd1 hb (energy_rate ht ht1 a b)
  simpa only [h, ENNReal.ofReal_mul (sq_nonneg _)] using ht

end SHEStochastic.SublinearHeatSpatialIncrement
