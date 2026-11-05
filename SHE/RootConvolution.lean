module

public import SHE.Kernels
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section
set_option autoImplicit false

/-! Exact clipped-root mass and finite Volterra convolution bounds. -/
noncomputable section
namespace SHE
open Set MeasureTheory

def rootMass (ν w : ℝ) : ℝ := ∫ t in (0 : ℝ)..w, rootKernel ν t

 theorem rootKernel_nonneg {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) :
    0 ≤ rootKernel ν t := by
  unfold rootKernel
  exact mul_nonneg (Real.rpow_nonneg ht _)
    (le_min (by norm_num) (mul_nonneg hν (Real.rpow_nonneg ht _)))

 theorem rootKernel_le_unclipped {ν t : ℝ} (ht : 0 < t) :
    rootKernel ν t ≤ ν * t ^ (-(3 / 4 : ℝ)) := by
  unfold rootKernel
  calc
    _ ≤ t ^ (-(1 : ℝ)) * (ν * t ^ (1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (Real.rpow_nonneg ht.le _)
    _ = ν * t ^ (-(3 / 4 : ℝ)) := by
      rw [mul_left_comm, ← Real.rpow_add ht]
      norm_num

 theorem rootKernel_continuousOn {ν w : ℝ} :
    ContinuousOn (rootKernel ν) (Ioc 0 w) := by
  apply continuousOn_of_forall_continuousAt
  intro t ht
  unfold rootKernel
  exact (continuousAt_id.rpow_const (Or.inl ht.1.ne')).mul
    (continuousAt_const.min (continuousAt_const.mul
      (continuousAt_id.rpow_const (Or.inl ht.1.ne'))))

 theorem rootKernel_intervalIntegrable {ν w : ℝ} (hν : 0 ≤ ν) (hw : 0 ≤ w) :
    IntervalIntegrable (rootKernel ν) volume 0 w := by
  have hg : IntervalIntegrable (fun t : ℝ => ν * t ^ (-(3 / 4 : ℝ))) volume 0 w :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(3 / 4 : ℝ))).const_mul ν
  apply hg.mono_fun'
  · rw [uIoc_of_le hw]
    exact rootKernel_continuousOn.aestronglyMeasurable measurableSet_Ioc
  · rw [uIoc_of_le hw]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (rootKernel_nonneg hν ht.1.le)]
    exact rootKernel_le_unclipped ht.1

 theorem rootMass_nonneg {ν w : ℝ} (hν : 0 ≤ ν) (hw : 0 ≤ w) :
    0 ≤ rootMass ν w := by
  apply intervalIntegral.integral_nonneg hw
  intro t ht
  exact rootKernel_nonneg hν ht.1

 theorem rootMass_mono {ν u w : ℝ} (hν : 0 ≤ ν) (hu : 0 ≤ u) (huw : u ≤ w) :
    rootMass ν u ≤ rootMass ν w := by
  apply intervalIntegral.integral_mono_interval le_rfl hu huw _
    (rootKernel_intervalIntegrable hν (hu.trans huw))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact rootKernel_nonneg hν ht.1.le

 theorem root_cutoff_identity {ν : ℝ} (hν : 0 < ν) :
    ν * (ν ^ (-(4 : ℝ))) ^ (1 / 4 : ℝ) = 1 := by
  rw [← Real.rpow_mul hν.le]
  norm_num
  simpa only [Real.rpow_neg_one] using mul_inv_cancel₀ hν.ne'

/-- Exact logarithmic root mass above the clipping scale. -/
theorem root_large_time_mass {ν w : ℝ} (hν : 0 < ν) (hcut : ν ^ (-(4 : ℝ)) ≤ w) :
    rootMass ν w = 4 + Real.log (ν ^ (4 : ℕ) * w) := by
  have hd : 0 < ν ^ (-(4 : ℝ)) := Real.rpow_pos_of_pos hν _
  have hw : 0 < w := hd.trans_le hcut
  have hid := root_cutoff_identity hν
  have hsmall : (∫ t in (0 : ℝ)..ν ^ (-(4 : ℝ)), rootKernel ν t) = 4 := by
    rw [root_small_time_mass hν.le hd.le hid.le]
    nlinarith [hid]
  have hft : IntervalIntegrable (rootKernel ν) volume (ν ^ (-(4 : ℝ))) w := by
    apply (rootKernel_intervalIntegrable hν.le hw.le).mono_set
    rw [uIcc_of_le hw.le, uIcc_of_le hcut]
    exact Icc_subset_Icc hd.le le_rfl
  unfold rootMass
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (rootKernel_intervalIntegrable hν.le hd.le) hft, hsmall]
  congr 1
  have heq : ∀ t ∈ Ioo (ν ^ (-(4 : ℝ))) w, rootKernel ν t = t⁻¹ := by
    intro t ht
    have ht0 : 0 < t := hd.trans ht.1
    have hc : 1 ≤ ν * t ^ (1 / 4 : ℝ) := by
      calc
        1 = ν * (ν ^ (-(4 : ℝ))) ^ (1 / 4 : ℝ) := hid.symm
        _ ≤ ν * t ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hd.le ht.1.le (by norm_num)) hν.le
    simp only [rootKernel, min_eq_left hc, Real.rpow_neg_one, mul_one]
  rw [intervalIntegral.integral_congr_Ioo_of_le hcut heq, integral_inv_of_pos hd hw]
  congr 1
  rw [Real.rpow_neg hν.le]
  norm_num [div_eq_mul_inv, mul_comm]

theorem rootKernel_measurable (ν : ℝ) : Measurable (rootKernel ν) := by
  apply measurable_of_continuousOn_compl_singleton 0
  apply continuousOn_of_forall_continuousAt
  intro t ht
  have ht0 : t ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using ht
  unfold rootKernel
  exact (continuousAt_id.rpow_const (Or.inl ht0)).mul
    (continuousAt_const.min (continuousAt_const.mul
      (continuousAt_id.rpow_const (Or.inl ht0))))

theorem rootKernel_eq_min {ν t : ℝ} (ht : 0 < t) :
    rootKernel ν t = min (t ^ (-(1 : ℝ))) (ν * t ^ (-(3 / 4 : ℝ))) := by
  unfold rootKernel
  rw [mul_min_of_nonneg _ _ (Real.rpow_nonneg ht.le _), mul_one]
  congr 1
  rw [mul_left_comm, ← Real.rpow_add ht]
  norm_num

theorem rootKernel_antitone {ν t w : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (htw : t ≤ w) :
    rootKernel ν w ≤ rootKernel ν t := by
  rw [rootKernel_eq_min ht, rootKernel_eq_min (ht.trans_le htw)]
  apply min_le_min
  · exact Real.rpow_le_rpow_of_nonpos ht htw (by norm_num)
  · exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ht htw (by norm_num)) hν

/-- The clipped amplitude is controlled by the exact root mass. -/
theorem root_clip_le_mass {ν w : ℝ} (hν : 0 ≤ ν) (hw : 0 ≤ w) :
    min 1 (ν * w ^ (1 / 4 : ℝ)) ≤ rootMass ν w := by
  by_cases hw0 : w = 0
  · simp [hw0, rootMass]
  have hwp : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
  have hi : (∫ _t in (0 : ℝ)..w, rootKernel ν w) ≤ rootMass ν w := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hw
      intervalIntegrable_const (rootKernel_intervalIntegrable hν hw)
    intro t ht
    exact rootKernel_antitone hν ht.1 ht.2.le
  have he : (∫ _t in (0 : ℝ)..w, rootKernel ν w) = min 1 (ν * w ^ (1 / 4 : ℝ)) := by
    rw [intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul, rootKernel, Real.rpow_neg_one]
    rw [← mul_assoc, mul_inv_cancel₀ hwp.ne', one_mul]
  rwa [he] at hi

/-- If a root interval occupies at least half the total time, its density
is at most twice the root density at the total time. -/
theorem rootKernel_le_twice {ν t w : ℝ} (hν : 0 ≤ ν) (hw : 0 < w)
    (htw : t ≤ w) (hhalf : w / 2 ≤ t) :
    rootKernel ν t ≤ 2 * rootKernel ν w := by
  have ht : 0 < t := by linarith
  have hc : min 1 (ν * t ^ (1 / 4 : ℝ)) ≤ min 1 (ν * w ^ (1 / 4 : ℝ)) := by
    apply min_le_min_left
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht.le htw (by norm_num)) hν
  have hi : t⁻¹ ≤ 2 * w⁻¹ := by
    have hd : 1 / t ≤ 2 / w := (div_le_div_iff₀ ht hw).mpr (by linarith)
    simpa only [div_eq_mul_inv, one_mul] using hd
  unfold rootKernel
  simp only [Real.rpow_neg_one]
  calc
    _ ≤ (2 * w⁻¹) * min 1 (ν * w ^ (1 / 4 : ℝ)) :=
      mul_le_mul hi hc (le_min (by norm_num) (mul_nonneg hν (Real.rpow_nonneg ht.le _)))
        (by positivity)
    _ = _ := by ring

/-- Symmetric integrable domination of the two-root convolution integrand. -/
theorem root_pair_le {ν t w : ℝ} (hν : 0 ≤ ν) (hw : 0 < w) (ht : t ∈ Ioo 0 w) :
    rootKernel ν t * rootKernel ν (w - t) ≤
      2 * rootKernel ν w * (rootKernel ν t + rootKernel ν (w - t)) := by
  have hn₁ := rootKernel_nonneg hν ht.1.le
  have hn₂ := rootKernel_nonneg hν (show 0 ≤ w - t by linarith [ht.2])
  have hn := rootKernel_nonneg hν hw.le
  by_cases hh : t ≤ w / 2
  · have hd : rootKernel ν (w - t) ≤ 2 * rootKernel ν w :=
      rootKernel_le_twice hν hw (by linarith [ht.1]) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hd hn₁]
  · have hd : rootKernel ν t ≤ 2 * rootKernel ν w :=
      rootKernel_le_twice hν hw ht.2.le (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hd hn₂]

theorem root_pair_intervalIntegrable {ν w : ℝ} (hν : 0 ≤ ν) (hw : 0 ≤ w) :
    IntervalIntegrable (fun t => rootKernel ν t * rootKernel ν (w - t)) volume 0 w := by
  have hr := rootKernel_intervalIntegrable hν hw
  have hsub : IntervalIntegrable (fun t => rootKernel ν (w - t)) volume 0 w := by
    simpa using (hr.comp_sub_left w).symm
  have hg := (hr.add hsub).const_mul (2 * rootKernel ν w)
  apply hg.mono_fun'
  · exact ((rootKernel_measurable ν).mul ((rootKernel_measurable ν).comp
      (measurable_const.sub measurable_id))).aestronglyMeasurable
  · rw [uIoc_of_le hw]
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (show ∀ᵐ t : ℝ ∂volume.restrict (Ioc 0 w), t ≠ w from
        (ae_restrict_of_ae (volume.ae_ne w)))] with t ht htw
    have ht' : t ∈ Ioo (0 : ℝ) w := ⟨ht.1, lt_of_le_of_ne ht.2 htw⟩
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (rootKernel_nonneg hν ht.1.le) (rootKernel_nonneg hν (by linarith [ht.2])))]
    exact root_pair_le hν (ht.1.trans ht'.2) ht'

/-- Two clipped roots convolve without losing the vanishing root mass. -/
theorem root_pair_convolution_le {ν w : ℝ} (hν : 0 ≤ ν) (hw : 0 ≤ w) :
    (∫ t in (0 : ℝ)..w, rootKernel ν t * rootKernel ν (w - t)) ≤
      4 * rootKernel ν w * rootMass ν w := by
  by_cases hw0 : w = 0
  · simp [hw0, rootMass]
  have hwp : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
  have hr := rootKernel_intervalIntegrable hν hw
  have hsub : IntervalIntegrable (fun t => rootKernel ν (w - t)) volume 0 w := by
    simpa using (hr.comp_sub_left w).symm
  calc
    _ ≤ ∫ t in (0 : ℝ)..w,
        2 * rootKernel ν w * (rootKernel ν t + rootKernel ν (w - t)) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hw
        (root_pair_intervalIntegrable hν hw) ((hr.add hsub).const_mul _)
      intro t ht
      exact root_pair_le hν hwp ht
    _ = 4 * rootKernel ν w * rootMass ν w := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hr hsub,
        intervalIntegral.integral_comp_sub_left]
      simp only [sub_self, sub_zero]
      unfold rootMass
      ring

/-- Volterra convolution, defined on all real times and zero at negative times. -/
def timeConvolution (f g : ℝ → ℝ) (w : ℝ) : ℝ :=
  ∫ t : ℝ, if 0 < t ∧ t ≤ w then f t * g (w - t) else 0

theorem timeConvolution_eq_intervalIntegral (f g : ℝ → ℝ) {w : ℝ} (hw : 0 ≤ w) :
    timeConvolution f g w = ∫ t in (0 : ℝ)..w, f t * g (w - t) := by
  rw [intervalIntegral.integral_of_le hw, timeConvolution]
  rw [← integral_indicator measurableSet_Ioc]
  congr 1
  funext t
  simp only [indicator_apply, mem_Ioc]

theorem timeConvolution_measurable {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (timeConvolution f g) := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      if 0 < p.2 ∧ p.2 ≤ p.1 then f p.2 * g (p.1 - p.2) else 0) := by
    apply Measurable.ite
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_fst))
    · exact (hf.comp measurable_snd).mul (hg.comp (measurable_fst.sub measurable_snd))
    · exact measurable_const
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- `rootWord ν n` is the convolution of `n+1` clipped root intervals. -/
def rootWord (ν : ℝ) : ℕ → ℝ → ℝ
  | 0 => rootKernel ν
  | n + 1 => timeConvolution (rootWord ν n) (rootKernel ν)

@[simp] theorem rootWord_zero (ν : ℝ) (n : ℕ) : rootWord ν n 0 = 0 := by
  cases n with
  | zero => simp [rootWord, rootKernel, Real.zero_rpow (by norm_num : (-1 : ℝ) ≠ 0)]
  | succ n => rw [rootWord, timeConvolution_eq_intervalIntegral _ _ le_rfl]; simp

theorem rootWord_measurable (ν : ℝ) (n : ℕ) : Measurable (rootWord ν n) := by
  induction n with
  | zero => exact rootKernel_measurable ν
  | succ n ih => exact timeConvolution_measurable ih (rootKernel_measurable ν)

theorem rootWord_nonneg {ν w : ℝ} (hν : 0 ≤ ν) (hw : 0 ≤ w) (n : ℕ) :
    0 ≤ rootWord ν n w := by
  induction n generalizing w with
  | zero => exact rootKernel_nonneg hν hw
  | succ n ih =>
    rw [rootWord, timeConvolution_eq_intervalIntegral _ _ hw]
    apply intervalIntegral.integral_nonneg hw
    intro t ht
    exact mul_nonneg (ih ht.1) (rootKernel_nonneg hν (by linarith [ht.2]))

/-- The finite-order all-root bound, proved by actual Volterra convolution induction.
In particular the exact mass remains present at every small-time corner. -/
theorem rootWord_le {ν w : ℝ} (hν : 0 ≤ ν) (hw : 0 ≤ w) (n : ℕ) :
    rootWord ν n w ≤ (4 : ℝ) ^ n * rootKernel ν w * rootMass ν w ^ n := by
  induction n generalizing w with
  | zero => simp [rootWord]
  | succ n ih =>
    have hnM := rootMass_nonneg hν hw
    have hdom : ∀ t ∈ Ioc (0 : ℝ) w,
        rootWord ν n t * rootKernel ν (w - t) ≤
          ((4 : ℝ) ^ n * rootMass ν w ^ n) *
            (rootKernel ν t * rootKernel ν (w - t)) := by
      intro t ht
      have hM : rootMass ν t ^ n ≤ rootMass ν w ^ n :=
        pow_le_pow_left₀ (rootMass_nonneg hν ht.1.le) (rootMass_mono hν ht.1.le ht.2) _
      have hnkt := rootKernel_nonneg hν ht.1.le
      have hnkw := rootKernel_nonneg hν (show 0 ≤ w - t by linarith [ht.2])
      calc
        _ ≤ ((4 : ℝ) ^ n * rootKernel ν t * rootMass ν t ^ n) * rootKernel ν (w - t) :=
          mul_le_mul_of_nonneg_right (ih ht.1.le) hnkw
        _ ≤ ((4 : ℝ) ^ n * rootKernel ν t * rootMass ν w ^ n) * rootKernel ν (w - t) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hM (mul_nonneg (by positivity) hnkt)) hnkw
        _ = _ := by ring
    have hfi : IntervalIntegrable
        (fun t => rootWord ν n t * rootKernel ν (w - t)) volume 0 w := by
      apply ((root_pair_intervalIntegrable hν hw).const_mul
        ((4 : ℝ) ^ n * rootMass ν w ^ n)).mono_fun'
      · exact ((rootWord_measurable ν n).mul ((rootKernel_measurable ν).comp
          (measurable_const.sub measurable_id))).aestronglyMeasurable
      · rw [uIoc_of_le hw]
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (rootWord_nonneg hν ht.1.le n) (rootKernel_nonneg hν (by linarith [ht.2])))]
        exact hdom t ht
    rw [rootWord, timeConvolution_eq_intervalIntegral _ _ hw]
    calc
      _ ≤ ∫ t in (0 : ℝ)..w, ((4 : ℝ) ^ n * rootMass ν w ^ n) *
          (rootKernel ν t * rootKernel ν (w - t)) := by
        apply intervalIntegral.integral_mono_on hw hfi
          ((root_pair_intervalIntegrable hν hw).const_mul _)
        intro t ht
        by_cases ht0 : t = 0
        · simp [ht0, rootWord_zero, rootKernel, Real.zero_rpow (by norm_num : (-1 : ℝ) ≠ 0)]
        · exact hdom t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩
      _ = ((4 : ℝ) ^ n * rootMass ν w ^ n) *
          (∫ t in (0 : ℝ)..w, rootKernel ν t * rootKernel ν (w - t)) :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ ((4 : ℝ) ^ n * rootMass ν w ^ n) *
          (4 * rootKernel ν w * rootMass ν w) :=
        mul_le_mul_of_nonneg_left (root_pair_convolution_le hν hw) (by positivity)
      _ = (4 : ℝ) ^ (n + 1) * rootKernel ν w * rootMass ν w ^ (n + 1) := by ring

theorem real_rpow_measurable (p : ℝ) : Measurable (fun t : ℝ => t ^ p) := by
  apply measurable_of_continuousOn_compl_singleton 0
  apply continuousOn_of_forall_continuousAt
  intro t ht
  apply Real.continuousAt_rpow_const
  left
  simpa only [mem_compl_iff, mem_singleton_iff] using ht

theorem positive_power_le_twice {B t w : ℝ} (hB : 0 ≤ B) (hw : 0 < w)
    (htw : t ≤ w) (hhalf : w / 2 ≤ t) :
    t ^ (B - 1) ≤ 2 * w ^ (B - 1) := by
  have ht : 0 < t := by linarith
  have hi : t⁻¹ ≤ 2 * w⁻¹ := by
    have hd : 1 / t ≤ 2 / w := (div_le_div_iff₀ ht hw).mpr (by linarith)
    simpa only [div_eq_mul_inv, one_mul] using hd
  calc
    t ^ (B - 1) = t ^ B * t⁻¹ := by rw [← Real.rpow_neg_one, ← Real.rpow_add ht]; congr 1
    _ ≤ w ^ B * (2 * w⁻¹) :=
      mul_le_mul (Real.rpow_le_rpow ht.le htw hB) hi (inv_nonneg.mpr ht.le)
        (Real.rpow_nonneg hw.le _)
    _ = 2 * w ^ (B - 1) := by
      rw [← Real.rpow_neg_one]
      calc
        _ = 2 * (w ^ B * w ^ (-(1 : ℝ))) := by ring
        _ = _ := by rw [← Real.rpow_add hw]; congr 1

theorem root_power_pair_le {ν B t w : ℝ} (hν : 0 ≤ ν) (hB : 0 < B)
    (hw : 0 < w) (ht : t ∈ Ioo 0 w) :
    t ^ (B - 1) * rootKernel ν (w - t) ≤
      2 * (w ^ (B - 1) * rootKernel ν (w - t) + rootKernel ν w * t ^ (B - 1)) := by
  have hn₁ := Real.rpow_nonneg ht.1.le (B - 1)
  have hn₂ := rootKernel_nonneg hν (show 0 ≤ w - t by linarith [ht.2])
  have hn := rootKernel_nonneg hν hw.le
  have hp := Real.rpow_nonneg hw.le (B - 1)
  by_cases hh : t ≤ w / 2
  · have hd : rootKernel ν (w - t) ≤ 2 * rootKernel ν w :=
      rootKernel_le_twice hν hw (by linarith [ht.1]) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hd hn₁]
  · have hd : t ^ (B - 1) ≤ 2 * w ^ (B - 1) :=
      positive_power_le_twice hB.le hw ht.2.le (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hd hn₂]

theorem root_power_pair_intervalIntegrable {ν B w : ℝ} (hν : 0 ≤ ν) (hB : 0 < B) (hw : 0 ≤ w) :
    IntervalIntegrable (fun t => t ^ (B - 1) * rootKernel ν (w - t)) volume 0 w := by
  have hr := rootKernel_intervalIntegrable hν hw
  have hsub : IntervalIntegrable (fun t => rootKernel ν (w - t)) volume 0 w := by
    simpa using (hr.comp_sub_left w).symm
  have hp : IntervalIntegrable (fun t : ℝ => t ^ (B - 1)) volume 0 w :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hg := ((hsub.const_mul (w ^ (B - 1))).add (hp.const_mul (rootKernel ν w))).const_mul 2
  apply hg.mono_fun'
  · exact ((real_rpow_measurable _).mul ((rootKernel_measurable ν).comp
      (measurable_const.sub measurable_id))).aestronglyMeasurable
  · rw [uIoc_of_le hw]
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (ae_restrict_of_ae (volume.ae_ne w))] with t ht htw
    have ht' : t ∈ Ioo (0 : ℝ) w := ⟨ht.1, lt_of_le_of_ne ht.2 htw⟩
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.rpow_nonneg ht.1.le _) (rootKernel_nonneg hν (by linarith [ht.2])))]
    exact root_power_pair_le hν hB (ht.1.trans ht'.2) ht'

/-- One root convolved with a positive-degree block retains the exact root mass. -/
theorem root_power_convolution_le {ν B w : ℝ} (hν : 0 ≤ ν) (hB : 0 < B) (hw : 0 < w) :
    (∫ t in (0 : ℝ)..w, t ^ (B - 1) * rootKernel ν (w - t)) ≤
      (2 * (1 + 1 / B)) * w ^ (B - 1) * rootMass ν w := by
  have hr := rootKernel_intervalIntegrable hν hw.le
  have hsub : IntervalIntegrable (fun t => rootKernel ν (w - t)) volume 0 w := by
    simpa using (hr.comp_sub_left w).symm
  have hp : IntervalIntegrable (fun t : ℝ => t ^ (B - 1)) volume 0 w :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hpm : (∫ t in (0 : ℝ)..w, t ^ (B - 1)) = w ^ B / B := by
    rw [integral_rpow (Or.inl (by linarith))]
    rw [show B - 1 + 1 = B by ring, Real.zero_rpow hB.ne', sub_zero]
  have hclip : rootKernel ν w * w ^ B ≤ w ^ (B - 1) * rootMass ν w := by
    calc
      _ = w ^ (B - 1) * min 1 (ν * w ^ (1 / 4 : ℝ)) := by
        unfold rootKernel
        rw [mul_assoc, mul_comm (min _ _) _, ← mul_assoc, ← Real.rpow_add hw]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (root_clip_le_mass hν hw.le) (Real.rpow_nonneg hw.le _)
  calc
    _ ≤ ∫ t in (0 : ℝ)..w,
        2 * (w ^ (B - 1) * rootKernel ν (w - t) + rootKernel ν w * t ^ (B - 1)) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hw.le
        (root_power_pair_intervalIntegrable hν hB hw.le)
        (((hsub.const_mul _).add (hp.const_mul _)).const_mul 2)
      intro t ht
      exact root_power_pair_le hν hB hw ht
    _ = 2 * (w ^ (B - 1) * rootMass ν w + rootKernel ν w * (w ^ B / B)) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
        (hsub.const_mul _) (hp.const_mul _), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, hpm, intervalIntegral.integral_comp_sub_left]
      simp only [sub_self, sub_zero, rootMass]
    _ ≤ 2 * (w ^ (B - 1) * rootMass ν w + (w ^ (B - 1) * rootMass ν w) / B) := by
      have he := div_le_div_of_nonneg_right hclip hB.le
      apply mul_le_mul_of_nonneg_left (add_le_add le_rfl _) (by norm_num : (0 : ℝ) ≤ 2)
      simpa only [mul_div_assoc] using he
    _ = _ := by ring

/-- A positive-degree rough block followed by `a` clipped root intervals. -/
def powerRootWord (ν B : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun w => w ^ (B - 1)
  | a + 1 => timeConvolution (powerRootWord ν B a) (rootKernel ν)

theorem powerRootWord_measurable (ν B : ℝ) (a : ℕ) : Measurable (powerRootWord ν B a) := by
  induction a with
  | zero => exact real_rpow_measurable _
  | succ a ih => exact timeConvolution_measurable ih (rootKernel_measurable ν)

theorem powerRootWord_nonneg {ν B w : ℝ} (hν : 0 ≤ ν) (hw : 0 ≤ w) (a : ℕ) :
    0 ≤ powerRootWord ν B a w := by
  induction a generalizing w with
  | zero => exact Real.rpow_nonneg hw _
  | succ a ih =>
    rw [powerRootWord, timeConvolution_eq_intervalIntegral _ _ hw]
    apply intervalIntegral.integral_nonneg hw
    intro t ht
    exact mul_nonneg (ih ht.1) (rootKernel_nonneg hν (by linarith [ht.2]))

/-- The positive-block convolution bound at every finite root order, with explicit constants. -/
theorem powerRootWord_le {ν B w : ℝ} (hν : 0 ≤ ν) (hB : 0 < B) (hw : 0 < w) (a : ℕ) :
    powerRootWord ν B a w ≤
      (2 * (1 + 1 / B)) ^ a * w ^ (B - 1) * rootMass ν w ^ a := by
  have hC : 0 ≤ 2 * (1 + 1 / B) := by positivity
  induction a generalizing w with
  | zero => simp [powerRootWord]
  | succ a ih =>
    have hnM := rootMass_nonneg hν hw.le
    have hdom : ∀ t ∈ Ioc (0 : ℝ) w,
        powerRootWord ν B a t * rootKernel ν (w - t) ≤
          ((2 * (1 + 1 / B)) ^ a * rootMass ν w ^ a) *
            (t ^ (B - 1) * rootKernel ν (w - t)) := by
      intro t ht
      have hM : rootMass ν t ^ a ≤ rootMass ν w ^ a :=
        pow_le_pow_left₀ (rootMass_nonneg hν ht.1.le) (rootMass_mono hν ht.1.le ht.2) _
      have hnkt := Real.rpow_nonneg ht.1.le (B - 1)
      have hnkw := rootKernel_nonneg hν (show 0 ≤ w - t by linarith [ht.2])
      calc
        _ ≤ ((2 * (1 + 1 / B)) ^ a * t ^ (B - 1) * rootMass ν t ^ a) * rootKernel ν (w - t) :=
          mul_le_mul_of_nonneg_right (ih ht.1) hnkw
        _ ≤ ((2 * (1 + 1 / B)) ^ a * t ^ (B - 1) * rootMass ν w ^ a) * rootKernel ν (w - t) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hM (mul_nonneg (pow_nonneg hC _) hnkt)) hnkw
        _ = _ := by ring
    have hfi : IntervalIntegrable
        (fun t => powerRootWord ν B a t * rootKernel ν (w - t)) volume 0 w := by
      apply ((root_power_pair_intervalIntegrable hν hB hw.le).const_mul
        ((2 * (1 + 1 / B)) ^ a * rootMass ν w ^ a)).mono_fun'
      · exact ((powerRootWord_measurable ν B a).mul ((rootKernel_measurable ν).comp
          (measurable_const.sub measurable_id))).aestronglyMeasurable
      · rw [uIoc_of_le hw.le]
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (powerRootWord_nonneg hν ht.1.le a) (rootKernel_nonneg hν (by linarith [ht.2])))]
        exact hdom t ht
    rw [powerRootWord, timeConvolution_eq_intervalIntegral _ _ hw.le]
    calc
      _ ≤ ∫ t in (0 : ℝ)..w, ((2 * (1 + 1 / B)) ^ a * rootMass ν w ^ a) *
          (t ^ (B - 1) * rootKernel ν (w - t)) := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo hw.le hfi
          ((root_power_pair_intervalIntegrable hν hB hw.le).const_mul _)
        intro t ht
        exact hdom t ⟨ht.1, ht.2.le⟩
      _ = ((2 * (1 + 1 / B)) ^ a * rootMass ν w ^ a) *
          (∫ t in (0 : ℝ)..w, t ^ (B - 1) * rootKernel ν (w - t)) :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ ((2 * (1 + 1 / B)) ^ a * rootMass ν w ^ a) *
          ((2 * (1 + 1 / B)) * w ^ (B - 1) * rootMass ν w) :=
        mul_le_mul_of_nonneg_left (root_power_convolution_le hν hB hw)
          (mul_nonneg (pow_nonneg hC _) (pow_nonneg hnM _))
      _ = (2 * (1 + 1 / B)) ^ (a + 1) * w ^ (B - 1) * rootMass ν w ^ (a + 1) := by ring

/-- The final positive-power convolution in the all-root corner. -/
theorem rootWord_final_power_le {ν B h : ℝ} (hν : 0 ≤ ν) (hB : 0 < B)
    (hh : 0 < h) (n : ℕ) :
    (∫ s in (0 : ℝ)..h, rootWord ν n (h - s) * s ^ (B - 1)) ≤
      ((4 : ℝ) ^ n * (2 * (1 + 1 / B))) * h ^ (B - 1) * rootMass ν h ^ (n + 1) := by
  have hM := rootMass_nonneg hν hh.le
  have hdom : ∀ s ∈ Icc (0 : ℝ) h,
      rootWord ν n (h - s) * s ^ (B - 1) ≤
        ((4 : ℝ) ^ n * rootMass ν h ^ n) * (s ^ (B - 1) * rootKernel ν (h - s)) := by
    intro s hs
    have hage : 0 ≤ h - s := by linarith [hs.2]
    have hm : rootMass ν (h - s) ^ n ≤ rootMass ν h ^ n :=
      pow_le_pow_left₀ (rootMass_nonneg hν hage)
        (rootMass_mono hν hage (by linarith [hs.1])) _
    have hk := rootKernel_nonneg hν hage
    have hp := Real.rpow_nonneg hs.1 (B - 1)
    calc
      _ ≤ ((4 : ℝ) ^ n * rootKernel ν (h - s) * rootMass ν (h - s) ^ n) * s ^ (B - 1) :=
        mul_le_mul_of_nonneg_right (rootWord_le hν hage n) hp
      _ ≤ ((4 : ℝ) ^ n * rootKernel ν (h - s) * rootMass ν h ^ n) * s ^ (B - 1) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hm (mul_nonneg (by positivity) hk)) hp
      _ = _ := by ring
  have hfi : IntervalIntegrable (fun s => rootWord ν n (h - s) * s ^ (B - 1)) volume 0 h := by
    apply ((root_power_pair_intervalIntegrable hν hB hh.le).const_mul
      ((4 : ℝ) ^ n * rootMass ν h ^ n)).mono_fun'
    · exact (((rootWord_measurable ν n).comp (measurable_const.sub measurable_id)).mul
        (real_rpow_measurable _)).aestronglyMeasurable
    · rw [uIoc_of_le hh.le]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (rootWord_nonneg hν (by linarith [hs.2]) n) (Real.rpow_nonneg hs.1.le _))]
      exact hdom s ⟨hs.1.le, hs.2⟩
  calc
    _ ≤ ∫ s in (0 : ℝ)..h,
        ((4 : ℝ) ^ n * rootMass ν h ^ n) * (s ^ (B - 1) * rootKernel ν (h - s)) := by
      apply intervalIntegral.integral_mono_on hh.le hfi
        ((root_power_pair_intervalIntegrable hν hB hh.le).const_mul _)
      exact hdom
    _ = ((4 : ℝ) ^ n * rootMass ν h ^ n) *
        (∫ s in (0 : ℝ)..h, s ^ (B - 1) * rootKernel ν (h - s)) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ ((4 : ℝ) ^ n * rootMass ν h ^ n) *
        ((2 * (1 + 1 / B)) * h ^ (B - 1) * rootMass ν h) :=
      mul_le_mul_of_nonneg_left (root_power_convolution_le hν hB hh) (by positivity)
    _ = _ := by ring

/-- The manuscript's final all-root corner, with arbitrary `σ > -1`.
This stronger bound retains the vanishing mass even below the cutoff. -/
theorem rootWord_final_corner_le {ν σ h : ℝ} (hν : 0 ≤ ν) (hσ : -1 < σ)
    (hh : 0 < h) (n : ℕ) :
    (∫ s in (0 : ℝ)..h, rootWord ν n (h - s) * s ^ σ) ≤
      ((4 : ℝ) ^ n * (2 * (1 + 1 / (σ + 1)))) * h ^ σ * rootMass ν h ^ (n + 1) := by
  have he := rootWord_final_power_le hν (show 0 < σ + 1 by linarith) hh n
  simpa only [add_sub_cancel_right] using he

theorem positive_power_pair_le {B C t w : ℝ} (hB : 0 < B) (hC : 0 < C)
    (hw : 0 < w) (ht : t ∈ Ioo 0 w) :
    t ^ (B - 1) * (w - t) ^ (C - 1) ≤
      2 * (w ^ (B - 1) * (w - t) ^ (C - 1) + w ^ (C - 1) * t ^ (B - 1)) := by
  have hn₁ := Real.rpow_nonneg ht.1.le (B - 1)
  have hn₂ := Real.rpow_nonneg (show 0 ≤ w - t by linarith [ht.2]) (C - 1)
  have hn := Real.rpow_nonneg hw.le (C - 1)
  have hp := Real.rpow_nonneg hw.le (B - 1)
  by_cases hh : t ≤ w / 2
  · have hd : (w - t) ^ (C - 1) ≤ 2 * w ^ (C - 1) :=
      positive_power_le_twice hC.le hw (by linarith [ht.1]) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hd hn₁]
  · have hd : t ^ (B - 1) ≤ 2 * w ^ (B - 1) :=
      positive_power_le_twice hB.le hw ht.2.le (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hd hn₂]

theorem positive_power_pair_intervalIntegrable {B C w : ℝ} (hB : 0 < B) (hC : 0 < C)
    (hw : 0 ≤ w) :
    IntervalIntegrable (fun t => t ^ (B - 1) * (w - t) ^ (C - 1)) volume 0 w := by
  have hp : IntervalIntegrable (fun t : ℝ => t ^ (B - 1)) volume 0 w :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hq : IntervalIntegrable (fun t : ℝ => (w - t) ^ (C - 1)) volume 0 w := by
    have hi : IntervalIntegrable (fun t : ℝ => t ^ (C - 1)) volume 0 w :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    simpa using (hi.comp_sub_left w).symm
  apply (((hq.const_mul (w ^ (B - 1))).add (hp.const_mul (w ^ (C - 1)))).const_mul 2).mono_fun'
  · exact ((real_rpow_measurable _).mul ((real_rpow_measurable _).comp
      (measurable_const.sub measurable_id))).aestronglyMeasurable
  · rw [uIoc_of_le hw]
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (ae_restrict_of_ae (volume.ae_ne w))] with t ht htw
    have ht' : t ∈ Ioo (0 : ℝ) w := ⟨ht.1, lt_of_le_of_ne ht.2 htw⟩
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.rpow_nonneg ht.1.le _) (Real.rpow_nonneg (by linarith [ht.2]) _))]
    exact positive_power_pair_le hB hC (ht.1.trans ht'.2) ht'

/-- An elementary Beta-integral bound, sufficient for every finite positive gap degree. -/
theorem positive_power_convolution_le {B C w : ℝ} (hB : 0 < B) (hC : 0 < C) (hw : 0 < w) :
    (∫ t in (0 : ℝ)..w, t ^ (B - 1) * (w - t) ^ (C - 1)) ≤
      2 * (1 / B + 1 / C) * w ^ (B + C - 1) := by
  have hp : IntervalIntegrable (fun t : ℝ => t ^ (B - 1)) volume 0 w :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hq : IntervalIntegrable (fun t : ℝ => (w - t) ^ (C - 1)) volume 0 w := by
    have hi : IntervalIntegrable (fun t : ℝ => t ^ (C - 1)) volume 0 w :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    simpa using (hi.comp_sub_left w).symm
  have hpm : (∫ t in (0 : ℝ)..w, t ^ (B - 1)) = w ^ B / B := by
    rw [integral_rpow (Or.inl (by linarith))]
    rw [show B - 1 + 1 = B by ring, Real.zero_rpow hB.ne', sub_zero]
  have hqm : (∫ t in (0 : ℝ)..w, (w - t) ^ (C - 1)) = w ^ C / C := by
    rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ (C - 1)) w]
    simp only [sub_self, sub_zero]
    rw [integral_rpow (Or.inl (by linarith))]
    rw [show C - 1 + 1 = C by ring, Real.zero_rpow hC.ne', sub_zero]
  have hpq : w ^ (B - 1) * w ^ C = w ^ (B + C - 1) := by
    rw [← Real.rpow_add hw]
    congr 1; ring
  have hqp : w ^ (C - 1) * w ^ B = w ^ (B + C - 1) := by
    rw [← Real.rpow_add hw]
    congr 1; ring
  calc
    _ ≤ ∫ t in (0 : ℝ)..w,
        2 * (w ^ (B - 1) * (w - t) ^ (C - 1) + w ^ (C - 1) * t ^ (B - 1)) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hw.le
        (positive_power_pair_intervalIntegrable hB hC hw.le)
        (((hq.const_mul _).add (hp.const_mul _)).const_mul 2)
      intro t ht
      exact positive_power_pair_le hB hC hw ht
    _ = 2 * (w ^ (B - 1) * (w ^ C / C) + w ^ (C - 1) * (w ^ B / B)) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
        (hq.const_mul _) (hp.const_mul _), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, hpm, hqm]
    _ = _ := by rw [← mul_div_assoc, ← mul_div_assoc, hpq, hqp]; ring

/-- The final positive-power corner after an arbitrary positive block and finitely many roots. -/
theorem powerRootWord_final_power_le {ν B C h : ℝ} (hν : 0 ≤ ν) (hB : 0 < B)
    (hC : 0 < C) (hh : 0 < h) (a : ℕ) :
    (∫ s in (0 : ℝ)..h, powerRootWord ν B a (h - s) * s ^ (C - 1)) ≤
      ((2 * (1 + 1 / B)) ^ a * (2 * (1 / B + 1 / C))) *
        h ^ (B + C - 1) * rootMass ν h ^ a := by
  have hM := rootMass_nonneg hν hh.le
  have hK : 0 ≤ 2 * (1 + 1 / B) := by positivity
  have hdom : ∀ s ∈ Ioo (0 : ℝ) h,
      powerRootWord ν B a (h - s) * s ^ (C - 1) ≤
        ((2 * (1 + 1 / B)) ^ a * rootMass ν h ^ a) *
          (s ^ (C - 1) * (h - s) ^ (B - 1)) := by
    intro s hs
    have hage : 0 < h - s := by linarith [hs.2]
    have hm : rootMass ν (h - s) ^ a ≤ rootMass ν h ^ a :=
      pow_le_pow_left₀ (rootMass_nonneg hν hage.le)
        (rootMass_mono hν hage.le (by linarith [hs.1])) _
    have hk := Real.rpow_nonneg hage.le (B - 1)
    have hp := Real.rpow_nonneg hs.1.le (C - 1)
    calc
      _ ≤ ((2 * (1 + 1 / B)) ^ a * (h - s) ^ (B - 1) * rootMass ν (h - s) ^ a) * s ^ (C - 1) :=
        mul_le_mul_of_nonneg_right (powerRootWord_le hν hB hage a) hp
      _ ≤ ((2 * (1 + 1 / B)) ^ a * (h - s) ^ (B - 1) * rootMass ν h ^ a) * s ^ (C - 1) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hm (mul_nonneg (pow_nonneg hK _) hk)) hp
      _ = _ := by ring
  have hfi : IntervalIntegrable
      (fun s => powerRootWord ν B a (h - s) * s ^ (C - 1)) volume 0 h := by
    apply ((positive_power_pair_intervalIntegrable hC hB hh.le).const_mul
      ((2 * (1 + 1 / B)) ^ a * rootMass ν h ^ a)).mono_fun'
    · exact (((powerRootWord_measurable ν B a).comp (measurable_const.sub measurable_id)).mul
        (real_rpow_measurable _)).aestronglyMeasurable
    · rw [uIoc_of_le hh.le]
      filter_upwards [ae_restrict_mem measurableSet_Ioc,
        ae_restrict_of_ae (volume.ae_ne h)] with s hs hsh
      have hs' : s ∈ Ioo (0 : ℝ) h := ⟨hs.1, lt_of_le_of_ne hs.2 hsh⟩
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (powerRootWord_nonneg hν (by linarith [hs.2]) a) (Real.rpow_nonneg hs.1.le _))]
      exact hdom s hs'
  calc
    _ ≤ ∫ s in (0 : ℝ)..h, ((2 * (1 + 1 / B)) ^ a * rootMass ν h ^ a) *
        (s ^ (C - 1) * (h - s) ^ (B - 1)) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hh.le hfi
        ((positive_power_pair_intervalIntegrable hC hB hh.le).const_mul _)
      exact hdom
    _ = ((2 * (1 + 1 / B)) ^ a * rootMass ν h ^ a) *
        (∫ s in (0 : ℝ)..h, s ^ (C - 1) * (h - s) ^ (B - 1)) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ ((2 * (1 + 1 / B)) ^ a * rootMass ν h ^ a) *
        (2 * (1 / C + 1 / B) * h ^ (C + B - 1)) :=
      mul_le_mul_of_nonneg_left (positive_power_convolution_le hC hB hh)
        (mul_nonneg (pow_nonneg hK _) (pow_nonneg hM _))
    _ = _ := by rw [add_comm C B]; ring

theorem powerRootWord_final_corner_le {ν B σ h : ℝ} (hν : 0 ≤ ν) (hB : 0 < B)
    (hσ : -1 < σ) (hh : 0 < h) (a : ℕ) :
    (∫ s in (0 : ℝ)..h, powerRootWord ν B a (h - s) * s ^ σ) ≤
      ((2 * (1 + 1 / B)) ^ a * (2 * (1 / B + 1 / (σ + 1)))) *
        h ^ (B + σ) * rootMass ν h ^ a := by
  have he := powerRootWord_final_power_le hν hB (show 0 < σ + 1 by linarith) hh a
  have hexp : B + (σ + 1) - 1 = B + σ := by ring
  simpa only [add_sub_cancel_right, hexp] using he

theorem rootMass_measurable (ν : ℝ) : Measurable (rootMass ν) := by
  have hpos : Measurable (fun p : ℝ × ℝ =>
      if 0 < p.2 ∧ p.2 ≤ p.1 then rootKernel ν p.2 else 0) := by
    apply Measurable.ite
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_fst))
    · exact (rootKernel_measurable ν).comp measurable_snd
    · exact measurable_const
  have hneg : Measurable (fun p : ℝ × ℝ =>
      if p.1 < p.2 ∧ p.2 ≤ 0 then rootKernel ν p.2 else 0) := by
    apply Measurable.ite
      ((measurableSet_lt measurable_fst measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const))
    · exact (rootKernel_measurable ν).comp measurable_snd
    · exact measurable_const
  have hm : Measurable (fun w : ℝ =>
      (∫ t : ℝ, if 0 < t ∧ t ≤ w then rootKernel ν t else 0) -
      (∫ t : ℝ, if w < t ∧ t ≤ 0 then rootKernel ν t else 0)) :=
    hpos.stronglyMeasurable.integral_prod_right'.measurable.sub
      hneg.stronglyMeasurable.integral_prod_right'.measurable
  convert hm using 1
  funext w
  unfold rootMass intervalIntegral
  rw [← integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Ioc]
  congr 1 <;> congr 1 <;> funext t <;> simp only [indicator_apply, mem_Ioc]

theorem root_mass_of_le_cutoff {ν w : ℝ} (hν : 0 < ν) (hw : 0 ≤ w)
    (hcut : w ≤ ν ^ (-(4 : ℝ))) :
    rootMass ν w = 4 * ν * w ^ (1 / 4 : ℝ) := by
  apply root_small_time_mass hν.le hw
  calc
    ν * w ^ (1 / 4 : ℝ) ≤ ν * (ν ^ (-(4 : ℝ))) ^ (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hw hcut (by norm_num)) hν.le
    _ = 1 := root_cutoff_identity hν

theorem root_mass_at_cutoff {ν : ℝ} (hν : 0 < ν) : rootMass ν (ν ^ (-(4 : ℝ))) = 4 := by
  rw [root_mass_of_le_cutoff hν (Real.rpow_nonneg hν.le _) le_rfl]
  nlinarith [root_cutoff_identity hν]

/-- The exact two-branch mass formula, including the singular small-time corner. -/
theorem root_mass_piecewise {ν w : ℝ} (hν : 0 < ν) (hw : 0 ≤ w) :
    rootMass ν w = if w ≤ ν ^ (-(4 : ℝ)) then 4 * ν * w ^ (1 / 4 : ℝ)
      else 4 + Real.log (ν ^ (4 : ℕ) * w) := by
  split_ifs with hc
  · exact root_mass_of_le_cutoff hν hw hc
  · exact root_large_time_mass hν (le_of_not_ge hc)

theorem root_mass_density_small_eq {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (hcut : t ≤ ν ^ (-(4 : ℝ))) (m : ℕ) :
    t⁻¹ * rootMass ν t ^ m = (4 * ν) ^ m * t ^ ((m : ℝ) / 4 - 1) := by
  rw [root_mass_of_le_cutoff hν ht.le hcut]
  rw [mul_pow, ← Real.rpow_mul_natCast ht.le, ← Real.rpow_neg_one]
  calc
    _ = (4 * ν) ^ m * (t ^ (-(1 : ℝ)) * t ^ ((1 / 4 : ℝ) * m)) := by ring
    _ = _ := by rw [← Real.rpow_add ht]; congr 2; ring

theorem root_mass_density_small_integrable {ν h : ℝ} (hν : 0 < ν) (hh : 0 ≤ h)
    (hcut : h ≤ ν ^ (-(4 : ℝ))) {m : ℕ} (hm : 0 < m) :
    IntervalIntegrable (fun t => t⁻¹ * rootMass ν t ^ m) volume 0 h := by
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have hi : IntervalIntegrable (fun t : ℝ => (4 * ν) ^ m * t ^ ((m : ℝ) / 4 - 1)) volume 0 h :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _
  apply hi.congr
  rw [uIoc_of_le hh]
  intro t ht
  exact (root_mass_density_small_eq hν ht.1 (ht.2.trans hcut) m).symm

/-- Exact square-corner primitive below the clipping scale, for every positive power. -/
theorem root_mass_density_small_integral {ν h : ℝ} (hν : 0 < ν) (hh : 0 ≤ h)
    (hcut : h ≤ ν ^ (-(4 : ℝ))) {m : ℕ} (hm : 0 < m) :
    (∫ t in (0 : ℝ)..h, t⁻¹ * rootMass ν t ^ m) =
      (4 / (m : ℝ)) * rootMass ν h ^ m := by
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have heq : ∀ t ∈ Ioo (0 : ℝ) h,
      t⁻¹ * rootMass ν t ^ m = (4 * ν) ^ m * t ^ ((m : ℝ) / 4 - 1) := by
    intro t ht
    exact root_mass_density_small_eq hν ht.1 (ht.2.le.trans hcut) m
  rw [intervalIntegral.integral_congr_Ioo_of_le hh heq, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith))]
  rw [show (m : ℝ) / 4 - 1 + 1 = (m : ℝ) / 4 by ring,
    Real.zero_rpow (by positivity : (m : ℝ) / 4 ≠ 0), sub_zero]
  rw [root_mass_of_le_cutoff hν hh hcut]
  simp only [mul_pow]
  rw [← Real.rpow_mul_natCast hh]
  rw [show (1 / 4 : ℝ) * m = (m : ℝ) / 4 by ring]
  ring

theorem root_mass_density_tail_integrable {ν h : ℝ} (hν : 0 < ν)
    (hcut : ν ^ (-(4 : ℝ)) ≤ h) (m : ℕ) :
    IntervalIntegrable (fun t => t⁻¹ * rootMass ν t ^ m) volume (ν ^ (-(4 : ℝ))) h := by
  have hd : 0 < ν ^ (-(4 : ℝ)) := Real.rpow_pos_of_pos hν _
  have hh : 0 < h := hd.trans_le hcut
  have hp : IntervalIntegrable (fun t : ℝ => t⁻¹) volume (ν ^ (-(4 : ℝ))) h := by
    have hi : IntervalIntegrable (fun t : ℝ => t ^ (-(1 : ℝ))) volume (ν ^ (-(4 : ℝ))) h := by
      apply intervalIntegral.intervalIntegrable_rpow (Or.inr _)
      rw [uIcc_of_le hcut]
      exact fun hz => (not_lt_of_ge hz.1) hd
    simpa only [Real.rpow_neg_one] using hi
  apply (hp.const_mul (rootMass ν h ^ m)).mono_fun'
  · exact (measurable_id.inv.mul ((rootMass_measurable ν).pow_const m)).aestronglyMeasurable
  · rw [uIoc_of_le hcut]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := hd.trans ht.1
    have hM := rootMass_nonneg hν.le ht0.le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr ht0.le) (pow_nonneg hM _))]
    calc
      _ ≤ t⁻¹ * rootMass ν h ^ m :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hM (rootMass_mono hν.le ht0.le ht.2) _) (inv_nonneg.mpr ht0.le)
      _ = _ := mul_comm _ _

theorem root_mass_density_tail_integral_le {ν h : ℝ} (hν : 0 < ν)
    (hcut : ν ^ (-(4 : ℝ)) ≤ h) (m : ℕ) :
    (∫ t in ν ^ (-(4 : ℝ))..h, t⁻¹ * rootMass ν t ^ m) ≤ rootMass ν h ^ (m + 1) := by
  have hd : 0 < ν ^ (-(4 : ℝ)) := Real.rpow_pos_of_pos hν _
  have hh : 0 < h := hd.trans_le hcut
  have hM := rootMass_nonneg hν.le hh.le
  have hp : IntervalIntegrable (fun t : ℝ => t⁻¹) volume (ν ^ (-(4 : ℝ))) h := by
    have hi : IntervalIntegrable (fun t : ℝ => t ^ (-(1 : ℝ))) volume (ν ^ (-(4 : ℝ))) h := by
      apply intervalIntegral.intervalIntegrable_rpow (Or.inr _)
      rw [uIcc_of_le hcut]
      exact fun hz => (not_lt_of_ge hz.1) hd
    simpa only [Real.rpow_neg_one] using hi
  have hlog : Real.log (h / ν ^ (-(4 : ℝ))) = rootMass ν h - 4 := by
    rw [root_large_time_mass hν hcut]
    have he : h / ν ^ (-(4 : ℝ)) = ν ^ (4 : ℕ) * h := by
      rw [Real.rpow_neg hν.le]
      norm_num [div_eq_mul_inv, mul_comm]
    rw [he]
    ring
  calc
    _ ≤ ∫ t in ν ^ (-(4 : ℝ))..h, rootMass ν h ^ m * t⁻¹ := by
      apply intervalIntegral.integral_mono_on hcut (root_mass_density_tail_integrable hν hcut m)
        (hp.const_mul _)
      intro t ht
      have ht0 : 0 < t := hd.trans_le ht.1
      calc
        _ ≤ t⁻¹ * rootMass ν h ^ m :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (rootMass_nonneg hν.le ht0.le)
            (rootMass_mono hν.le ht0.le ht.2) _) (inv_nonneg.mpr ht0.le)
        _ = _ := mul_comm _ _
    _ = rootMass ν h ^ m * (rootMass ν h - 4) := by
      rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hd hh, hlog]
    _ ≤ rootMass ν h ^ m * rootMass ν h :=
      mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hM _)
    _ = _ := by ring

theorem root_mass_density_integrable {ν h : ℝ} (hν : 0 < ν) (hh : 0 ≤ h)
    {m : ℕ} (hm : 0 < m) :
    IntervalIntegrable (fun t => t⁻¹ * rootMass ν t ^ m) volume 0 h := by
  by_cases hc : h ≤ ν ^ (-(4 : ℝ))
  · exact root_mass_density_small_integrable hν hh hc hm
  · exact (root_mass_density_small_integrable hν (Real.rpow_nonneg hν.le _) le_rfl hm).trans
      (root_mass_density_tail_integrable hν (le_of_not_ge hc) m)

/-- Every positive mass power controls the all-root square-time singularity. -/
theorem root_mass_density_integral_le {ν h : ℝ} (hν : 0 < ν) (hh : 0 ≤ h)
    {m : ℕ} (hm : 0 < m) :
    (∫ t in (0 : ℝ)..h, t⁻¹ * rootMass ν t ^ m) ≤
      (4 / (m : ℝ) + rootMass ν h) * rootMass ν h ^ m := by
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have hM := rootMass_nonneg hν.le hh
  by_cases hc : h ≤ ν ^ (-(4 : ℝ))
  · rw [root_mass_density_small_integral hν hh hc hm]
    nlinarith [mul_nonneg hM (pow_nonneg hM m)]
  · have hcut : ν ^ (-(4 : ℝ)) ≤ h := le_of_not_ge hc
    have hd : 0 ≤ ν ^ (-(4 : ℝ)) := Real.rpow_nonneg hν.le _
    have hsmall := root_mass_density_small_integrable hν hd le_rfl hm
    have htail := root_mass_density_tail_integrable hν hcut m
    rw [← intervalIntegral.integral_add_adjacent_intervals hsmall htail,
      root_mass_density_small_integral hν hd le_rfl hm, root_mass_at_cutoff hν]
    have hm0 : 4 ≤ rootMass ν h := by
      rw [← root_mass_at_cutoff hν]
      exact rootMass_mono hν.le hd hcut
    have hmpow : (4 : ℝ) ^ m ≤ rootMass ν h ^ m := pow_le_pow_left₀ (by norm_num) hm0 _
    calc
      _ ≤ (4 / (m : ℝ)) * rootMass ν h ^ m + rootMass ν h ^ (m + 1) :=
        add_le_add (mul_le_mul_of_nonneg_left hmpow (by positivity))
          (root_mass_density_tail_integral_le hν hcut m)
      _ = _ := by ring

/-- Explicit all-root Ito-corner bound with the manuscript's single extra mass power. -/
theorem root_mass_square_corner_le {ν h : ℝ} (hν : 0 < ν) (hh : 0 ≤ h)
    {a : ℕ} (ha : 0 < a) :
    (∫ t in (0 : ℝ)..h, t⁻¹ * rootMass ν t ^ (2 * a)) ≤
      (1 + 4 / (2 * a : ℕ)) * (1 + rootMass ν h) ^ (2 * a + 1) := by
  have hm : 0 < 2 * a := Nat.mul_pos (by norm_num) ha
  have hmp : (0 : ℝ) < (2 * a : ℕ) := by exact_mod_cast hm
  have hM := rootMass_nonneg hν.le hh
  have hp : rootMass ν h ^ (2 * a) ≤ (1 + rootMass ν h) ^ (2 * a) :=
    pow_le_pow_left₀ hM (by linarith) _
  calc
    _ ≤ (4 / (2 * a : ℕ) + rootMass ν h) * rootMass ν h ^ (2 * a) :=
      root_mass_density_integral_le hν hh hm
    _ ≤ ((1 + 4 / (2 * a : ℕ)) * (1 + rootMass ν h)) * (1 + rootMass ν h) ^ (2 * a) := by
      apply mul_le_mul _ hp (pow_nonneg hM _) _
      · have hc : 0 ≤ 4 / ((2 * a : ℕ) : ℝ) := by positivity
        nlinarith [mul_nonneg hc hM]
      · positivity
    _ = _ := by ring

/-- A positive external degree makes the square-time singularity integrable directly. -/
theorem weighted_root_mass_pos_le {ν d h : ℝ} (hν : 0 ≤ ν) (hd : 0 < d)
    (hh : 0 ≤ h) (m : ℕ) :
    (∫ t in (0 : ℝ)..h, t ^ (d - 1) * rootMass ν t ^ m) ≤
      h ^ d / d * rootMass ν h ^ m := by
  have hM := rootMass_nonneg hν hh
  have hp : IntervalIntegrable (fun t : ℝ => t ^ (d - 1)) volume 0 h :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hdom : ∀ t ∈ Ioc (0 : ℝ) h,
      t ^ (d - 1) * rootMass ν t ^ m ≤ rootMass ν h ^ m * t ^ (d - 1) := by
    intro t ht
    calc
      _ ≤ t ^ (d - 1) * rootMass ν h ^ m :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (rootMass_nonneg hν ht.1.le) (rootMass_mono hν ht.1.le ht.2) _)
          (Real.rpow_nonneg ht.1.le _)
      _ = _ := mul_comm _ _
  have hfi : IntervalIntegrable (fun t => t ^ (d - 1) * rootMass ν t ^ m) volume 0 h := by
    apply (hp.const_mul (rootMass ν h ^ m)).mono_fun'
    · exact ((real_rpow_measurable _).mul ((rootMass_measurable ν).pow_const m)).aestronglyMeasurable
    · rw [uIoc_of_le hh]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _)
        (pow_nonneg (rootMass_nonneg hν ht.1.le) _))]
      exact hdom t ht
  calc
    _ ≤ ∫ t in (0 : ℝ)..h, rootMass ν h ^ m * t ^ (d - 1) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hh hfi (hp.const_mul _)
      intro t ht
      exact hdom t ⟨ht.1, ht.2.le⟩
    _ = h ^ d / d * rootMass ν h ^ m := by
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
        show d - 1 + 1 = d by ring, Real.zero_rpow hd.ne', sub_zero]
      ring

theorem weighted_root_density_small_eq {ν d t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (hcut : t ≤ ν ^ (-(4 : ℝ))) (m : ℕ) :
    t ^ (d - 1) * rootMass ν t ^ m =
      (4 * ν) ^ m * t ^ (d + (m : ℝ) / 4 - 1) := by
  rw [root_mass_of_le_cutoff hν ht.le hcut, mul_pow, ← Real.rpow_mul_natCast ht.le]
  calc
    _ = (4 * ν) ^ m * (t ^ (d - 1) * t ^ ((1 / 4 : ℝ) * m)) := by ring
    _ = _ := by rw [← Real.rpow_add ht]; congr 2; ring

theorem cutoff_rpow_cancel {ν p q : ℝ} (hν : 0 < ν) :
    ν ^ p * (ν ^ (-(4 : ℝ))) ^ q = ν ^ (p - 4 * q) := by
  rw [← Real.rpow_mul hν.le, ← Real.rpow_add hν]
  congr 1
  ring

theorem weighted_root_small_integrable {ν d h : ℝ} (hν : 0 < ν) (hh : 0 ≤ h)
    (hcut : h ≤ ν ^ (-(4 : ℝ))) {m : ℕ} (hdeg : 0 < d + (m : ℝ) / 4) :
    IntervalIntegrable (fun t => t ^ (d - 1) * rootMass ν t ^ m) volume 0 h := by
  have hi : IntervalIntegrable
      (fun t : ℝ => (4 * ν) ^ m * t ^ (d + (m : ℝ) / 4 - 1)) volume 0 h :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _
  apply hi.congr
  rw [uIoc_of_le hh]
  intro t ht
  exact (weighted_root_density_small_eq hν ht.1 (ht.2.trans hcut) m).symm

/-- The complete small-scale weighted square integral, with its exact frequency power. -/
theorem weighted_root_small_cutoff_integral {ν d : ℝ} (hν : 0 < ν)
    {m : ℕ} (hdeg : 0 < d + (m : ℝ) / 4) :
    (∫ t in (0 : ℝ)..ν ^ (-(4 : ℝ)), t ^ (d - 1) * rootMass ν t ^ m) =
      ((4 : ℝ) ^ m / (d + (m : ℝ) / 4)) * ν ^ (-4 * d) := by
  have hd : 0 ≤ ν ^ (-(4 : ℝ)) := Real.rpow_nonneg hν.le _
  rw [intervalIntegral.integral_congr_Ioo_of_le hd (fun t ht =>
    weighted_root_density_small_eq hν ht.1 ht.2.le m), intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith)),
    show d + (m : ℝ) / 4 - 1 + 1 = d + (m : ℝ) / 4 by ring,
    Real.zero_rpow hdeg.ne', sub_zero]
  rw [mul_pow, ← Real.rpow_natCast ν m]
  calc
    _ = ((4 : ℝ) ^ m / (d + (m : ℝ) / 4)) *
        (ν ^ (m : ℝ) * (ν ^ (-(4 : ℝ))) ^ (d + (m : ℝ) / 4)) := by ring
    _ = _ := by rw [cutoff_rpow_cancel hν]; congr 2; ring

/-- Above the cutoff, root mass is bounded by every positive rescaled power. -/
theorem root_mass_le_rescaled_power {ν ε t : ℝ} (hν : 0 < ν) (hε : 0 < ε)
    (hcut : ν ^ (-(4 : ℝ)) ≤ t) :
    rootMass ν t ≤ (4 + 1 / ε) * ν ^ (4 * ε) * t ^ ε := by
  have hd : 0 < ν ^ (-(4 : ℝ)) := Real.rpow_pos_of_pos hν _
  have ht : 0 < t := hd.trans_le hcut
  have hx : 1 ≤ ν ^ (4 : ℕ) * t := by
    have hmul := mul_le_mul_of_nonneg_left hcut (pow_nonneg hν.le 4)
    have he : ν ^ (4 : ℕ) * ν ^ (-(4 : ℝ)) = 1 := by
      rw [← Real.rpow_natCast ν 4, ← Real.rpow_add hν]
      norm_num
    rwa [he] at hmul
  have hxε := Real.one_le_rpow hx hε.le
  have hlog := Real.log_le_rpow_div (show 0 ≤ ν ^ (4 : ℕ) * t by positivity) hε
  rw [root_large_time_mass hν hcut]
  calc
    _ ≤ (4 + 1 / ε) * (ν ^ (4 : ℕ) * t) ^ ε := by
      simp only [div_eq_mul_inv] at hlog ⊢
      nlinarith
    _ = _ := by
      rw [Real.mul_rpow (pow_nonneg hν.le _) ht.le, ← Real.rpow_natCast ν 4,
        ← Real.rpow_mul hν.le]
      norm_num
      ring

theorem weighted_root_tail_pointwise {ν d ε t : ℝ} (hν : 0 < ν) (hε : 0 < ε)
    (hcut : ν ^ (-(4 : ℝ)) ≤ t) (m : ℕ) :
    t ^ (d - 1) * rootMass ν t ^ m ≤
      ((4 + 1 / ε) ^ m * ν ^ (4 * ε * m)) * t ^ (d + ε * m - 1) := by
  have ht : 0 < t := (Real.rpow_pos_of_pos hν (-(4 : ℝ))).trans_le hcut
  have hM := rootMass_nonneg hν.le ht.le
  calc
    _ ≤ t ^ (d - 1) * ((4 + 1 / ε) * ν ^ (4 * ε) * t ^ ε) ^ m :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM (root_mass_le_rescaled_power hν hε hcut) _)
        (Real.rpow_nonneg ht.le _)
    _ = ((4 + 1 / ε) ^ m * ν ^ (4 * ε * m)) * (t ^ (d - 1) * t ^ (ε * m)) := by
      simp only [mul_pow]
      rw [← Real.rpow_mul_natCast hν.le, ← Real.rpow_mul_natCast ht.le]
      ring
    _ = _ := by rw [← Real.rpow_add ht]; congr 2; ring

theorem negative_power_tail_le {α c h : ℝ} (hα : α < 0) (hc : 0 < c) (hch : c ≤ h) :
    (∫ t in c..h, t ^ (α - 1)) ≤ c ^ α / (-α) := by
  have hz : (0 : ℝ) ∉ uIcc c h := by
    rw [uIcc_of_le hch]
    exact fun ht => (not_lt_of_ge ht.1) hc
  rw [integral_rpow (Or.inr ⟨by linarith, hz⟩), show α - 1 + 1 = α by ring]
  calc
    _ = (c ^ α - h ^ α) / (-α) := by ring
    _ ≤ c ^ α / (-α) :=
      div_le_div_of_nonneg_right (by linarith [Real.rpow_nonneg (hc.le.trans hch) α]) (by linarith)

theorem weighted_root_tail_integrable {ν d ε h : ℝ} (hν : 0 < ν) (hε : 0 < ε)
    (hcut : ν ^ (-(4 : ℝ)) ≤ h) (m : ℕ) :
    IntervalIntegrable (fun t => t ^ (d - 1) * rootMass ν t ^ m) volume (ν ^ (-(4 : ℝ))) h := by
  have hd : 0 < ν ^ (-(4 : ℝ)) := Real.rpow_pos_of_pos hν _
  have hp : IntervalIntegrable (fun t : ℝ => t ^ (d + ε * m - 1)) volume (ν ^ (-(4 : ℝ))) h := by
    apply intervalIntegral.intervalIntegrable_rpow (Or.inr _)
    rw [uIcc_of_le hcut]
    exact fun hz => (not_lt_of_ge hz.1) hd
  apply (hp.const_mul ((4 + 1 / ε) ^ m * ν ^ (4 * ε * m))).mono_fun'
  · exact ((real_rpow_measurable _).mul ((rootMass_measurable ν).pow_const m)).aestronglyMeasurable
  · rw [uIoc_of_le hcut]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := hd.trans ht.1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _)
      (pow_nonneg (rootMass_nonneg hν.le ht0.le) _))]
    exact weighted_root_tail_pointwise hν hε ht.1.le m

theorem weighted_root_tail_integral_le {ν d ε h : ℝ} (hν : 0 < ν) (hε : 0 < ε)
    (hcut : ν ^ (-(4 : ℝ)) ≤ h) {m : ℕ} (hdeg : d + ε * m < 0) :
    (∫ t in ν ^ (-(4 : ℝ))..h, t ^ (d - 1) * rootMass ν t ^ m) ≤
      ((4 + 1 / ε) ^ m / (-(d + ε * m))) * ν ^ (-4 * d) := by
  have hd : 0 < ν ^ (-(4 : ℝ)) := Real.rpow_pos_of_pos hν _
  have hp : IntervalIntegrable (fun t : ℝ => t ^ (d + ε * m - 1)) volume (ν ^ (-(4 : ℝ))) h := by
    apply intervalIntegral.intervalIntegrable_rpow (Or.inr _)
    rw [uIcc_of_le hcut]
    exact fun hz => (not_lt_of_ge hz.1) hd
  have hCoeff : 0 ≤ (4 + 1 / ε) ^ m * ν ^ (4 * ε * m) := by positivity
  calc
    _ ≤ ∫ t in ν ^ (-(4 : ℝ))..h,
        ((4 + 1 / ε) ^ m * ν ^ (4 * ε * m)) * t ^ (d + ε * m - 1) := by
      apply intervalIntegral.integral_mono_on hcut (weighted_root_tail_integrable hν hε hcut m)
        (hp.const_mul _)
      intro t ht
      exact weighted_root_tail_pointwise hν hε ht.1 m
    _ = ((4 + 1 / ε) ^ m * ν ^ (4 * ε * m)) *
        (∫ t in ν ^ (-(4 : ℝ))..h, t ^ (d + ε * m - 1)) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ ((4 + 1 / ε) ^ m * ν ^ (4 * ε * m)) *
        ((ν ^ (-(4 : ℝ))) ^ (d + ε * m) / (-(d + ε * m))) :=
      mul_le_mul_of_nonneg_left (negative_power_tail_le hdeg hd hcut) hCoeff
    _ = ((4 + 1 / ε) ^ m / (-(d + ε * m))) *
        (ν ^ (4 * ε * m) * (ν ^ (-(4 : ℝ))) ^ (d + ε * m)) := by ring
    _ = _ := by rw [cutoff_rpow_cancel hν]; congr 2; ring

/-- A parameterized negative-degree square bound, including its required small-scale condition. -/
theorem weighted_root_negative_aux {d ε : ℝ} {m : ℕ} (hε : 0 < ε)
    (hsmall : 0 < d + (m : ℝ) / 4) (hlarge : d + ε * m < 0)
    {ν h : ℝ} (hν : 0 < ν) (hh : 0 ≤ h) :
    (∫ t in (0 : ℝ)..h, t ^ (d - 1) * rootMass ν t ^ m) ≤
      ((4 : ℝ) ^ m / (d + (m : ℝ) / 4) +
        (4 + 1 / ε) ^ m / (-(d + ε * m))) * ν ^ (-4 * d) := by
  have hd : 0 < ν ^ (-(4 : ℝ)) := Real.rpow_pos_of_pos hν _
  have hsmallint := weighted_root_small_integrable hν hd.le le_rfl hsmall
  have hden : 0 < -(d + ε * m) := by linarith
  have htailnonneg : 0 ≤ ((4 + 1 / ε) ^ m / (-(d + ε * m))) * ν ^ (-4 * d) := by positivity
  by_cases hc : h ≤ ν ^ (-(4 : ℝ))
  · calc
      _ ≤ ∫ t in (0 : ℝ)..ν ^ (-(4 : ℝ)), t ^ (d - 1) * rootMass ν t ^ m := by
        apply intervalIntegral.integral_mono_interval le_rfl hh hc _ hsmallint
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact mul_nonneg (Real.rpow_nonneg ht.1.le _) (pow_nonneg (rootMass_nonneg hν.le ht.1.le) _)
      _ = ((4 : ℝ) ^ m / (d + (m : ℝ) / 4)) * ν ^ (-4 * d) :=
        weighted_root_small_cutoff_integral hν hsmall
      _ ≤ _ := by nlinarith
  · have hcut : ν ^ (-(4 : ℝ)) ≤ h := le_of_not_ge hc
    rw [← intervalIntegral.integral_add_adjacent_intervals hsmallint
      (weighted_root_tail_integrable hν hε hcut m), weighted_root_small_cutoff_integral hν hsmall]
    have he := weighted_root_tail_integral_le hν hε hcut hlarge
    nlinarith

/-- The negative-degree branch has exactly the state-frequency power in the manuscript. -/
theorem weighted_root_negative {d : ℝ} (hd : d < 0) {m : ℕ} (hm : 0 < m)
    (hsmall : 0 < d + (m : ℝ) / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ν h : ℝ), 0 < ν → 0 ≤ h →
      (∫ t in (0 : ℝ)..h, t ^ (d - 1) * rootMass ν t ^ m) ≤ C * ν ^ (-4 * d) := by
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  let ε : ℝ := -d / (2 * m)
  have hε : 0 < ε := by
    dsimp [ε]
    exact div_pos (by linarith) (mul_pos (by norm_num) hmp)
  have he : d + ε * m = d / 2 := by dsimp [ε]; field_simp; ring
  have hlarge : d + ε * m < 0 := by rw [he]; linarith
  have hden : 0 < -(d + ε * m) := by linarith
  refine ⟨(4 : ℝ) ^ m / (d + (m : ℝ) / 4) +
    (4 + 1 / ε) ^ m / (-(d + ε * m)), ?_, ?_⟩
  · positivity
  · intro ν h hν hh
    exact weighted_root_negative_aux hε hsmall hlarge hν hh

/-- All three weighted square regimes refer to convergent integrals. -/
theorem weighted_root_integrable {ν d h : ℝ} (hν : 0 < ν) (hh : 0 ≤ h)
    {m : ℕ} (hdeg : 0 < d + (m : ℝ) / 4) :
    IntervalIntegrable (fun t => t ^ (d - 1) * rootMass ν t ^ m) volume 0 h := by
  by_cases hc : h ≤ ν ^ (-(4 : ℝ))
  · exact weighted_root_small_integrable hν hh hc hdeg
  · exact (weighted_root_small_integrable hν (Real.rpow_nonneg hν.le _) le_rfl hdeg).trans
      (weighted_root_tail_integrable hν (by norm_num : (0 : ℝ) < 1) (le_of_not_ge hc) m)

/-- The negative native-current branch specializes to `ν^(2χ-4ρ)`. -/
theorem native_root_square_negative {ρ χ : ℝ} (hρ : 0 < ρ) (hχ : χ < 1)
    (hcase : 2 * ρ < χ) {a : ℕ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ν h : ℝ), 0 < ν → 0 ≤ h →
      (∫ t in (0 : ℝ)..h, t ^ (ρ - χ / 2 - 1) * rootMass ν t ^ (2 * a)) ≤
        C * ν ^ (2 * χ - 4 * ρ) := by
  have hm : 0 < 2 * a := Nat.mul_pos (by norm_num) ha
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hdeg : 0 < (ρ - χ / 2) + ((2 * a : ℕ) : ℝ) / 4 := by
    push_cast
    linarith
  obtain ⟨C, hC, hb⟩ := weighted_root_negative (d := ρ - χ / 2) (by linarith) hm hdeg
  refine ⟨C, hC, ?_⟩
  intro ν h hν hh
  have he := hb ν h hν hh
  have hexp : -4 * (ρ - χ / 2) = 2 * χ - 4 * ρ := by ring
  simpa only [hexp] using he

end SHE
