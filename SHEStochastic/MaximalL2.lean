module

public import SHE.LpEnergy
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Measure.WithDensity

/-! The deterministic layer-cake step behind Doob's L² inequality. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.MaximalL2
open MeasureTheory Set
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {S Y : Ω → ℝ}

def WeakBound (S Y : Ω → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → ENNReal.ofReal t * μ {ω | t ≤ S ω} ≤
    ∫⁻ ω in {ω | t ≤ S ω}, ENNReal.ofReal (Y ω) ∂μ

theorem tail_bound (hS : Measurable S) (hY : Measurable Y)
    (hSn : ∀ ω, 0 ≤ S ω) (hYn : ∀ ω, 0 ≤ Y ω) (hweak : WeakBound μ S Y) :
    (∫⁻ ω, ENNReal.ofReal (S ω ^ 2) ∂μ) ≤
      2 * ∫⁻ ω, ENNReal.ofReal (S ω * Y ω) ∂μ := by
  let ν := μ.withDensity (fun ω => ENNReal.ofReal (Y ω))
  have hl := lintegral_rpow_eq_lintegral_meas_le_mul μ
    (Filter.Eventually.of_forall hSn) hS.aemeasurable (p := 2) (by norm_num)
  norm_num only [Real.rpow_two, sub_self, add_sub_cancel_left, Real.rpow_one,
    show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.ofReal_ofNat] at hl
  have hw : (∫⁻ ω, ENNReal.ofReal (S ω) ∂ν) =
      ∫⁻ ω, ENNReal.ofReal (S ω * Y ω) ∂μ := by
    rw [lintegral_withDensity_eq_lintegral_mul μ hY.ennreal_ofReal hS.ennreal_ofReal]
    apply lintegral_congr
    intro ω
    change ENNReal.ofReal (Y ω) * ENNReal.ofReal (S ω) = _
    rw [← ENNReal.ofReal_mul (hYn ω), mul_comm]
  calc
    _ = 2 * ∫⁻ t in Ioi (0 : ℝ), μ {ω | t ≤ S ω} * ENNReal.ofReal t := hl
    _ ≤ 2 * ∫⁻ t in Ioi (0 : ℝ), ν {ω | t ≤ S ω} := by
      refine mul_le_mul_right ?_ (2 : ℝ≥0∞)
      apply lintegral_mono_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      rw [show ν {ω | t ≤ S ω} =
        ∫⁻ ω in {ω | t ≤ S ω}, ENNReal.ofReal (Y ω) ∂μ from
        withDensity_apply _ (measurableSet_le measurable_const hS)]
      simpa only [mul_comm] using hweak t ht
    _ = 2 * ∫⁻ ω, ENNReal.ofReal (S ω) ∂ν := by
      rw [lintegral_eq_lintegral_meas_le ν (Filter.Eventually.of_forall hSn) hS.aemeasurable]
    _ = _ := by rw [hw]

/-- The strong L² estimate follows from the weak maximal inequality
and ordinary Hilbert Cauchy--Schwarz, whenever the maximum is in L². -/
theorem strong_bound (hS : Measurable S) (hY : Measurable Y)
    (hSn : ∀ ω, 0 ≤ S ω) (hYn : ∀ ω, 0 ≤ Y ω)
    (hs : MemLp S 2 μ) (hy : MemLp Y 2 μ) (hweak : WeakBound μ S Y) :
    (∫ ω, S ω ^ 2 ∂μ) ≤ 4 * ∫ ω, Y ω ^ 2 ∂μ := by
  let s := hs.toLp S
  let y := hy.toLp Y
  have hsn : ‖s‖ ^ 2 = ∫ ω, S ω ^ 2 ∂μ := by
    rw [SHE.PredictableL2.realLp_norm_sq]
    apply integral_congr_ae
    filter_upwards [hs.coeFn_toLp] with ω hω
    rw [show s ω = S ω from hω, Real.norm_eq_abs, sq_abs]
  have hyn : ‖y‖ ^ 2 = ∫ ω, Y ω ^ 2 ∂μ := by
    rw [SHE.PredictableL2.realLp_norm_sq]
    apply integral_congr_ae
    filter_upwards [hy.coeFn_toLp] with ω hω
    rw [show y ω = Y ω from hω, Real.norm_eq_abs, sq_abs]
  have hinner : inner ℝ s y = ∫ ω, S ω * Y ω ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hs.coeFn_toLp, hy.coeFn_toLp] with ω hsω hyω
    simp only [show s ω = S ω from hsω, show y ω = Y ω from hyω,
      RCLike.inner_apply, conj_trivial, mul_comm]
  have hreal : (∫ ω, S ω ^ 2 ∂μ) ≤ 2 * ∫ ω, S ω * Y ω ∂μ := by
    have hSY : Integrable (fun ω => S ω * Y ω) μ := hs.integrable_mul hy
    have h := tail_bound μ hS hY hSn hYn hweak
    rw [← ofReal_integral_eq_lintegral_ofReal hs.integrable_sq
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _)),
      ← ofReal_integral_eq_lintegral_ofReal hSY
        (Filter.Eventually.of_forall (fun ω => mul_nonneg (hSn ω) (hYn ω))),
      ← ENNReal.ofReal_ofNat (n := 2), ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at h
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by norm_num)
      (integral_nonneg (fun ω => mul_nonneg (hSn ω) (hYn ω))))).mp h
  rw [← hsn, ← hinner] at hreal
  have hnorm : ‖s‖ ≤ 2 * ‖y‖ := by
    by_cases hz : ‖s‖ = 0
    · simp [hz]
    · have hp : 0 < ‖s‖ := lt_of_le_of_ne (norm_nonneg s) (Ne.symm hz)
      apply (mul_le_mul_iff_right₀ hp).mp
      nlinarith [real_inner_le_norm s y]
  rw [← hsn, ← hyn]
  nlinarith [pow_le_pow_left₀ (norm_nonneg s) hnorm 2]

theorem weak_min (hweak : WeakBound μ S Y) (R : ℝ) :
    WeakBound μ (fun ω => min (S ω) R) Y := by
  intro t ht
  by_cases h : t ≤ R
  · simpa only [le_min_iff, and_iff_left h] using hweak t ht
  · have hempty : {ω | t ≤ min (S ω) R} = ∅ := by ext ω; simp [le_min_iff, h]
    simp only [hempty, measure_empty, mul_zero, Measure.restrict_empty, lintegral_zero_measure, le_refl]

/-- Truncation removes any assumption that the maximum already lies in
L². This is the non-circular form needed for Doob's inequality. -/
theorem lintegral_bound [IsFiniteMeasure μ] (hS : Measurable S) (hY : Measurable Y)
    (hSn : ∀ ω, 0 ≤ S ω) (hYn : ∀ ω, 0 ≤ Y ω)
    (hy : MemLp Y 2 μ) (hweak : WeakBound μ S Y) :
    (∫⁻ ω, ENNReal.ofReal (S ω ^ 2) ∂μ) ≤
      4 * ∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂μ := by
  let f (n : ℕ) (ω : Ω) := min (S ω) (n : ℝ)
  have hfn (n : ℕ) (ω : Ω) : 0 ≤ f n ω := le_min (hSn ω) (Nat.cast_nonneg n)
  have hfm (n : ℕ) : Measurable (f n) := hS.min measurable_const
  have hmem (n : ℕ) : MemLp (f n) 2 μ := by
    apply MemLp.of_bound (hfm n).aestronglyMeasurable (n : ℝ)
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hfn n ω)]
    exact min_le_right _ _
  have hb (n : ℕ) : (∫⁻ ω, ENNReal.ofReal (f n ω ^ 2) ∂μ) ≤
      4 * ∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂μ := by
    have h := ENNReal.ofReal_le_ofReal (strong_bound μ (hfm n) hY (hfn n) hYn
      (hmem n) hy (weak_min μ hweak n))
    rw [ofReal_integral_eq_lintegral_ofReal (hmem n).integrable_sq
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _)),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat,
      ofReal_integral_eq_lintegral_ofReal hy.integrable_sq
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _))] at h
    exact h
  have hm : ∀ ω, Monotone (fun n => ENNReal.ofReal (f n ω ^ 2)) := by
    intro ω i j hij
    apply ENNReal.ofReal_le_ofReal
    exact pow_le_pow_left₀ (hfn i ω) (min_le_min_left _ (Nat.cast_le.mpr hij)) 2
  have ht (ω : Ω) : Filter.Tendsto (fun n => ENNReal.ofReal (f n ω ^ 2))
      Filter.atTop (𝓝 (ENNReal.ofReal (S ω ^ 2))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop ⌈S ω⌉₊] with n hn
    have hs : S ω ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    simp only [f, min_eq_left hs]
  have hlim := lintegral_tendsto_of_tendsto_of_monotone (μ := μ)
    (fun n => ((hfm n).pow_const 2).ennreal_ofReal.aemeasurable)
    (Filter.Eventually.of_forall hm) (Filter.Eventually.of_forall ht)
  exact le_of_tendsto hlim (Filter.Eventually.of_forall hb)

end SHEStochastic.MaximalL2
