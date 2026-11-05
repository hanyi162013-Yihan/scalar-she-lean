module

public import SHE.Kernels

@[expose] public section
set_option autoImplicit false

/-! Scalar new-time bounds with arbitrary nonnegative endpoint offsets.
The constants are explicit and uniform in the offsets. -/
noncomputable section
namespace SHE
open Set MeasureTheory

/-- The endpoint-pair integrand in the first-hit new-time estimate. -/
def newTimeKernel (Λ s bi bj τ : ℝ) : ℝ :=
  min 1 (Λ * (τ + bi)) * (τ + bi) ^ (-(1 / 2 : ℝ) - s) *
    (τ + bj) ^ (-(1 / 2 : ℝ))

 theorem newTimeKernel_nonneg {Λ s bi bj τ : ℝ} (hΛ : 0 ≤ Λ)
    (hbi : 0 ≤ bi) (hbj : 0 ≤ bj) (hτ : 0 ≤ τ) :
    0 ≤ newTimeKernel Λ s bi bj τ := by
  unfold newTimeKernel
  exact mul_nonneg (mul_nonneg (le_min (by norm_num) (mul_nonneg hΛ (by linarith)))
    (Real.rpow_nonneg (by linarith) _)) (Real.rpow_nonneg (by linarith) _)

/-- The clipped input factor has a finite maximum even at a singular endpoint. -/
theorem clipped_input_le {Λ s a : ℝ} (hΛ : 0 ≤ Λ) (ha : 0 < a)
    (hs : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    min 1 (Λ * a) * a ^ (-(1 / 2 : ℝ) - s) ≤ Λ ^ ((1 / 2 : ℝ) + s) := by
  calc
    _ ≤ (Λ * a) ^ ((1 / 2 : ℝ) + s) * a ^ (-(1 / 2 : ℝ) - s) :=
      mul_le_mul_of_nonneg_right
        (min_one_le_rpow (mul_nonneg hΛ ha.le) (by linarith) (by linarith))
        (Real.rpow_nonneg ha.le _)
    _ = Λ ^ ((1 / 2 : ℝ) + s) := by
      rw [Real.mul_rpow hΛ ha.le]
      rw [mul_assoc, ← Real.rpow_add ha]
      norm_num

/-- At short new times, only the companion endpoint singularity remains. -/
theorem newTimeKernel_le_short {Λ s bi bj τ : ℝ} (hΛ : 0 ≤ Λ)
    (hbi : 0 ≤ bi) (hbj : 0 ≤ bj) (hτ : 0 < τ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    newTimeKernel Λ s bi bj τ ≤
      Λ ^ ((1 / 2 : ℝ) + s) * τ ^ (-(1 / 2 : ℝ)) := by
  unfold newTimeKernel
  exact mul_le_mul (clipped_input_le hΛ (by linarith) hs hs1)
    (Real.rpow_le_rpow_of_nonpos hτ (by linarith) (by norm_num))
    (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg hΛ _)

/-- At long new times, the equal-age power bounds every pair of offsets. -/
theorem newTimeKernel_le_long {Λ s bi bj τ : ℝ} (_hΛ : 0 ≤ Λ)
    (hbi : 0 ≤ bi) (hbj : 0 ≤ bj) (hτ : 0 < τ) (hs : 0 ≤ s) :
    newTimeKernel Λ s bi bj τ ≤ τ ^ (-1 - s) := by
  have hi : (τ + bi) ^ (-(1 / 2 : ℝ) - s) ≤ τ ^ (-(1 / 2 : ℝ) - s) :=
    Real.rpow_le_rpow_of_nonpos hτ (by linarith) (by linarith)
  have hj : (τ + bj) ^ (-(1 / 2 : ℝ)) ≤ τ ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hτ (by linarith) (by norm_num)
  calc
    _ ≤ 1 * (τ + bi) ^ (-(1 / 2 : ℝ) - s) * (τ + bj) ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg (by linarith) _))
        (Real.rpow_nonneg (by linarith) _)
    _ ≤ τ ^ (-(1 / 2 : ℝ) - s) * τ ^ (-(1 / 2 : ℝ)) := by
      simpa using mul_le_mul hi hj (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg hτ.le _)
    _ = τ ^ (-1 - s) := by rw [← Real.rpow_add hτ]; congr 1; ring

 theorem newTimeKernel_continuousOn {Λ s bi bj H : ℝ} (hbi : 0 ≤ bi) (hbj : 0 ≤ bj) :
    ContinuousOn (newTimeKernel Λ s bi bj) (Ioc 0 H) := by
  apply continuousOn_of_forall_continuousAt
  intro τ hτ
  unfold newTimeKernel
  have hi : τ + bi ≠ 0 := by linarith [hτ.1]
  have hj : τ + bj ≠ 0 := by linarith [hτ.1]
  exact ((continuousAt_const.min (continuousAt_const.mul
    (continuousAt_id.add continuousAt_const))).mul
    ((continuousAt_id.add continuousAt_const).rpow_const (Or.inl hi))).mul
    ((continuousAt_id.add continuousAt_const).rpow_const (Or.inl hj))

/-- Actual integrability, including when either or both endpoint offsets vanish. -/
theorem newTimeKernel_intervalIntegrable {Λ s bi bj H : ℝ} (hΛ : 0 ≤ Λ)
    (hbi : 0 ≤ bi) (hbj : 0 ≤ bj) (hH : 0 ≤ H)
    (hs : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    IntervalIntegrable (newTimeKernel Λ s bi bj) volume 0 H := by
  have hg : IntervalIntegrable (fun τ : ℝ =>
      Λ ^ ((1 / 2 : ℝ) + s) * τ ^ (-(1 / 2 : ℝ))) volume 0 H :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))).const_mul _
  apply hg.mono_fun'
  · rw [uIoc_of_le hH]
    exact (newTimeKernel_continuousOn hbi hbj).aestronglyMeasurable measurableSet_Ioc
  · rw [uIoc_of_le hH]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
    rw [Real.norm_eq_abs, abs_of_nonneg (newTimeKernel_nonneg hΛ hbi hbj hτ.1.le)]
    exact newTimeKernel_le_short hΛ hbi hbj hτ.1 hs hs1

/-- Exact integral of the short-time majorant at the cutoff. -/
theorem short_majorant_mass {Λ s : ℝ} (hΛ : 0 < Λ) :
    (∫ τ in (0 : ℝ)..Λ⁻¹,
      Λ ^ ((1 / 2 : ℝ) + s) * τ ^ (-(1 / 2 : ℝ))) = 2 * Λ ^ s := by
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))]
  norm_num
  rw [Real.inv_rpow hΛ.le, ← Real.rpow_neg hΛ.le]
  calc
    _ = 2 * (Λ ^ ((1 / 2 : ℝ) + s) * Λ ^ (-(1 / 2 : ℝ))) := by ring
    _ = 2 * Λ ^ s := by rw [← Real.rpow_add hΛ]; congr 2; ring

/-- Uniform bound below the cutoff, with no assumptions on the offset sizes. -/
theorem newTimeKernel_integral_short {Λ s bi bj H : ℝ} (hΛ : 0 < Λ)
    (hbi : 0 ≤ bi) (hbj : 0 ≤ bj) (hH : 0 ≤ H) (hcut : H ≤ Λ⁻¹)
    (hs : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    (∫ τ in (0 : ℝ)..H, newTimeKernel Λ s bi bj τ) ≤ 2 * Λ ^ s := by
  have hgi : ∀ B : ℝ, IntervalIntegrable (fun τ : ℝ =>
      Λ ^ ((1 / 2 : ℝ) + s) * τ ^ (-(1 / 2 : ℝ))) volume 0 B := fun B =>
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))).const_mul _
  calc
    _ ≤ ∫ τ in (0 : ℝ)..H,
        Λ ^ ((1 / 2 : ℝ) + s) * τ ^ (-(1 / 2 : ℝ)) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hH
        (newTimeKernel_intervalIntegrable hΛ.le hbi hbj hH hs hs1) (hgi H)
      intro τ hτ
      exact newTimeKernel_le_short hΛ.le hbi hbj hτ.1 hs hs1
    _ ≤ ∫ τ in (0 : ℝ)..Λ⁻¹,
        Λ ^ ((1 / 2 : ℝ) + s) * τ ^ (-(1 / 2 : ℝ)) := by
      apply intervalIntegral.integral_mono_interval le_rfl hH hcut _ (hgi _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
      exact mul_nonneg (Real.rpow_nonneg hΛ.le _) (Real.rpow_nonneg hτ.1.le _)
    _ = 2 * Λ ^ s := short_majorant_mass hΛ

/-- Splitting at the reciprocal cutoff reduces the long part to a pure power. -/
theorem newTimeKernel_integral_split {Λ s bi bj H : ℝ} (hΛ : 0 < Λ)
    (hbi : 0 ≤ bi) (hbj : 0 ≤ bj) (hcut : Λ⁻¹ ≤ H)
    (hs : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    (∫ τ in (0 : ℝ)..H, newTimeKernel Λ s bi bj τ) ≤
      2 * Λ ^ s + ∫ τ in Λ⁻¹..H, τ ^ (-1 - s) := by
  have hd : 0 < Λ⁻¹ := inv_pos.mpr hΛ
  have hH : 0 ≤ H := hd.le.trans hcut
  have hf := newTimeKernel_intervalIntegrable hΛ.le hbi hbj hH hs hs1
  have hfd := newTimeKernel_intervalIntegrable hΛ.le hbi hbj hd.le hs hs1
  have hft : IntervalIntegrable (newTimeKernel Λ s bi bj) volume Λ⁻¹ H := by
    apply hf.mono_set
    rw [uIcc_of_le hH, uIcc_of_le hcut]
    exact Icc_subset_Icc hd.le le_rfl
  have hgt : IntervalIntegrable (fun τ : ℝ => τ ^ (-1 - s)) volume Λ⁻¹ H := by
    apply intervalIntegral.intervalIntegrable_rpow (Or.inr _)
    rw [uIcc_of_le hcut]
    exact fun hz => (not_lt_of_ge hz.1) hd
  rw [← intervalIntegral.integral_add_adjacent_intervals hfd hft]
  apply add_le_add (newTimeKernel_integral_short hΛ hbi hbj hd.le le_rfl hs hs1)
  apply intervalIntegral.integral_mono_on hcut hft hgt
  intro τ hτ
  exact newTimeKernel_le_long hΛ.le hbi hbj (hd.trans_le hτ.1) hs

/-- The long-time power tail has a cutoff-uniform bound for every positive order. -/
theorem long_power_mass_le {Λ s H : ℝ} (hΛ : 0 < Λ) (hs : 0 < s)
    (hcut : Λ⁻¹ ≤ H) :
    (∫ τ in Λ⁻¹..H, τ ^ (-1 - s)) ≤ Λ ^ s / s := by
  have hd : 0 < Λ⁻¹ := inv_pos.mpr hΛ
  have hH : 0 < H := hd.trans_le hcut
  have hzero : (0 : ℝ) ∉ uIcc Λ⁻¹ H := by
    rw [uIcc_of_le hcut]
    exact fun hz => (not_lt_of_ge hz.1) hd
  rw [integral_rpow (Or.inr ⟨by linarith, hzero⟩)]
  have hexp : (-1 : ℝ) - s + 1 = -s := by ring
  rw [hexp, Real.inv_rpow hΛ.le, ← Real.rpow_neg hΛ.le, neg_neg]
  have hnonneg : 0 ≤ H ^ (-s) := Real.rpow_nonneg hH.le _
  calc
    (H ^ (-s) - Λ ^ s) / -s = (Λ ^ s - H ^ (-s)) / s := by ring
    _ ≤ Λ ^ s / s := div_le_div_of_nonneg_right (by linarith) hs.le

/-- The positive-order new-time estimate, uniformly over every nonnegative offset.
The manuscript's range `0 < s < 1/2` is included; the endpoint `s = 1/2` also holds. -/
theorem new_time_integral_power {Λ s bi bj H : ℝ} (hΛ : 0 < Λ)
    (hbi : 0 ≤ bi) (hbj : 0 ≤ bj) (hH : 0 ≤ H)
    (hs : 0 < s) (hs1 : s ≤ 1 / 2) :
    (∫ τ in (0 : ℝ)..H, newTimeKernel Λ s bi bj τ) ≤
      (2 + 1 / s) * Λ ^ s := by
  by_cases hcut : H ≤ Λ⁻¹
  · calc
      _ ≤ 2 * Λ ^ s := newTimeKernel_integral_short hΛ hbi hbj hH hcut hs.le hs1
      _ ≤ (2 + 1 / s) * Λ ^ s := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hΛ.le _)
        have : 0 ≤ 1 / s := le_of_lt (one_div_pos.mpr hs)
        linarith
  · have hdH : Λ⁻¹ ≤ H := le_of_not_ge hcut
    calc
      _ ≤ 2 * Λ ^ s + ∫ τ in Λ⁻¹..H, τ ^ (-1 - s) :=
        newTimeKernel_integral_split hΛ hbi hbj hdH hs.le hs1
      _ ≤ 2 * Λ ^ s + Λ ^ s / s :=
        add_le_add le_rfl (long_power_mass_le hΛ hs hdH)
      _ = (2 + 1 / s) * Λ ^ s := by ring

/-- The zeroth-order new-time estimate grows only logarithmically in the horizon. -/
theorem new_time_integral_log {Λ bi bj H h : ℝ} (hΛ : 0 < Λ)
    (hbi : 0 ≤ bi) (hbj : 0 ≤ bj) (hH : 0 ≤ H) (hHh : H ≤ h) :
    (∫ τ in (0 : ℝ)..H, newTimeKernel Λ 0 bi bj τ) ≤
      2 + Real.log (2 + Λ * h) := by
  have hh : 0 ≤ h := hH.trans hHh
  have hlog : 0 ≤ Real.log (2 + Λ * h) :=
    Real.log_nonneg (by nlinarith [mul_nonneg hΛ.le hh])
  by_cases hcut : H ≤ Λ⁻¹
  · have he := newTimeKernel_integral_short hΛ hbi hbj hH hcut
      (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    simp only [Real.rpow_zero, mul_one] at he
    exact he.trans (by linarith)
  · have hdH : Λ⁻¹ ≤ H := le_of_not_ge hcut
    have hd : 0 < Λ⁻¹ := inv_pos.mpr hΛ
    have hHp : 0 < H := hd.trans_le hdH
    have htail : (∫ τ in Λ⁻¹..H, τ ^ (-1 - (0 : ℝ))) = Real.log (Λ * H) := by
      simp only [sub_zero, Real.rpow_neg_one]
      rw [integral_inv_of_pos hd hHp]
      congr 1
      simp [div_eq_mul_inv, mul_comm]
    have hlogmono : Real.log (Λ * H) ≤ Real.log (2 + Λ * h) := by
      apply Real.log_le_log (mul_pos hΛ hHp)
      nlinarith [mul_le_mul_of_nonneg_left hHh hΛ.le]
    have he := newTimeKernel_integral_split hΛ hbi hbj hdH
      (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [Real.rpow_zero, mul_one, htail] at he
    exact he.trans (add_le_add le_rfl hlogmono)

/-- Direct explicit-constant form of the manuscript's logarithmic estimate. -/
theorem new_time_integral_log_manuscript {Λ bi bj H h : ℝ} (hΛ : 1 ≤ Λ)
    (hbi : 0 ≤ bi) (hbj : 0 ≤ bj) (hH : 0 ≤ H) (hHh : H ≤ h) :
    (∫ τ in (0 : ℝ)..H, newTimeKernel Λ 0 bi bj τ) ≤
      2 * (1 + Real.log (2 + Λ * h)) := by
  have hΛp : 0 < Λ := by linarith
  have hh : 0 ≤ h := hH.trans hHh
  have hlog : 0 ≤ Real.log (2 + Λ * h) :=
    Real.log_nonneg (by nlinarith [mul_nonneg hΛp.le hh])
  exact (new_time_integral_log hΛp hbi hbj hH hHh).trans (by linarith)

end SHE
