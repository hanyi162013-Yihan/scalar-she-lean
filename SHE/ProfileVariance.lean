module

public import SHE.HistoryFrames

@[expose] public section
set_option autoImplicit false

/-! The actual physical heat-square covariance map for bounded measurable profiles. -/
noncomputable section
namespace SHE.ProfileVariance
open Set MeasureTheory AddCircle StoppedFourier
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

def heatPhysical (t : ℝ) (x y : HeatCircle) : ℂ := heatCrossKernel t y x

theorem heatPhysical_measurable (x : HeatCircle) :
    Measurable (fun p : ℝ × HeatCircle => heatPhysical p.1 x p.2) := by
  unfold heatPhysical heatCrossKernel
  apply Measurable.tsum
  intro n
  have he : Measurable (fun p : ℝ × HeatCircle => (Real.exp (-p.1 * (n : ℝ) ^ 2) : ℂ)) := by fun_prop
  exact (he.mul ((fourier n).continuous.measurable.comp measurable_snd)).mul measurable_const

theorem heatPhysical_ae {t : ℝ} (ht : 0 < t) (x : HeatCircle) :
    heatPhysical t x =ᵐ[haarAddCircle] (circleHeat t x : HeatCircle → ℂ) := by
  have hh : 0 < t / 2 := by positivity
  have hk : heatPhysical t x = fun y => inner ℂ (circleHeat (t / 2) y) (circleHeat (t / 2) x) := by
    funext y
    simpa only [heatPhysical, show t / 2 + t / 2 = t by ring] using
      (circleHeat_cross_gram hh hh y x).symm
  have ho : circleHeatOperator (t / 2) hh.le (circleHeat (t / 2) x) = circleHeat t x := by
    simpa only [show t / 2 + t / 2 = t by ring] using circleHeatOperator_heat hh.le hh x
  rw [hk]
  simpa only [ho] using heat_kernel_inner_ae hh (circleHeat (t / 2) x)

theorem heatPhysical_square_integrable {t : ℝ} (ht : 0 < t) (x : HeatCircle) :
    Integrable (fun y => ‖heatPhysical t x y‖ ^ 2) haarAddCircle := by
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.memLp (circleHeat t x)).aestronglyMeasurable).mp
    (Lp.memLp (circleHeat t x))
  exact hi.congr (by filter_upwards [heatPhysical_ae ht x] with y hy; rw [hy])

theorem heatPhysical_square_mass {t : ℝ} (ht : 0 < t) (x : HeatCircle) :
    (∫ y, ‖heatPhysical t x y‖ ^ 2 ∂haarAddCircle) = ‖circleHeat t x‖ ^ 2 := by
  rw [L2_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [heatPhysical_ae ht x] with y hy
  rw [hy]

def varianceDensity (c : ℝ × HeatCircle → ℝ) (r : ℝ) (x : HeatCircle) (s : ℝ) : ℝ :=
  ∫ y : HeatCircle, ‖heatPhysical (r - s) x y‖ ^ 2 * c (s, y) ∂haarAddCircle

def varianceMap (c : ℝ × HeatCircle → ℝ) (r : ℝ) (x : HeatCircle) : ℝ :=
  ∫ s in (0 : ℝ)..r, varianceDensity c r x s

theorem varianceDensity_measurable {c : ℝ × HeatCircle → ℝ} (hc : Measurable c)
    (r : ℝ) (x : HeatCircle) : Measurable (varianceDensity c r x) := by
  have hk : Measurable (fun p : ℝ × HeatCircle => heatPhysical (r - p.1) x p.2) :=
    (heatPhysical_measurable x).comp ((measurable_const.sub measurable_fst).prodMk measurable_snd)
  exact (((hk.norm.pow_const (2 : ℕ)).mul hc).stronglyMeasurable.integral_prod_right).measurable

theorem varianceDensity_integrable {c : ℝ × HeatCircle → ℝ} {r s C : ℝ}
    (hc : Measurable c) (_hC : 0 ≤ C) (hs : s < r)
    (hbound : ∀ y, |c (s, y)| ≤ C) (x : HeatCircle) :
    Integrable (fun y : HeatCircle => ‖heatPhysical (r - s) x y‖ ^ 2 * c (s, y)) haarAddCircle := by
  have hi := (heatPhysical_square_integrable (sub_pos.mpr hs) x).mul_const C
  have hm : Measurable (fun y : HeatCircle => ‖heatPhysical (r - s) x y‖ ^ 2 * c (s, y)) := by
    have hk : Measurable (fun y : HeatCircle => heatPhysical (r - s) x y) :=
      (heatPhysical_measurable x).comp (measurable_const.prodMk measurable_id)
    have hc' : Measurable (fun y : HeatCircle => c (s, y)) :=
      hc.comp (measurable_const.prodMk measurable_id)
    exact (hk.norm.pow_const (2 : ℕ)).mul hc'
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left (hbound y) (sq_nonneg _)

theorem varianceDensity_bound {c : ℝ × HeatCircle → ℝ} {r s C : ℝ}
    (hc : Measurable c) (hC : 0 ≤ C) (hs : s < r)
    (hbound : ∀ y, |c (s, y)| ≤ C) (x : HeatCircle) :
    |varianceDensity c r x s| ≤ C * ‖circleHeat (r - s) x‖ ^ 2 := by
  unfold varianceDensity
  rw [← Real.norm_eq_abs]
  calc
    _ ≤ ∫ y : HeatCircle, ‖‖heatPhysical (r - s) x y‖ ^ 2 * c (s, y)‖ ∂haarAddCircle :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y : HeatCircle, ‖heatPhysical (r - s) x y‖ ^ 2 * C ∂haarAddCircle := by
      apply integral_mono (varianceDensity_integrable hc hC hs hbound x).norm
        ((heatPhysical_square_integrable (sub_pos.mpr hs) x).mul_const C)
      intro y
      change ‖‖heatPhysical (r - s) x y‖ ^ 2 * c (s, y)‖ ≤ ‖heatPhysical (r - s) x y‖ ^ 2 * C
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hbound y) (sq_nonneg _)
    _ = _ := by rw [integral_mul_const, heatPhysical_square_mass (sub_pos.mpr hs)]; ring

theorem heat_mass_small_time {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (x : HeatCircle) :
    ‖circleHeat t x‖ ^ 2 ≤ (1 + heatConstant) * t ^ (-(1 / 2 : ℝ)) := by
  have hb := circleHeat_norm_sq_bound ht x
  have hp : 1 ≤ t ^ (-(1 / 2 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1 (by norm_num)
  nlinarith

theorem heat_mass_time_integral {r : ℝ} (_hr : 0 < r) :
    (∫ s in (0 : ℝ)..r, (r - s) ^ (-(1 / 2 : ℝ))) = 2 * r ^ (1 / 2 : ℝ) := by
  rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) r]
  simp only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))]
  norm_num [Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  ring

/-- The actual heat-square covariance map has norm of order `√r` on bounded
measurable signed profiles; both spatial and time convergence are proved. -/
theorem varianceMap_bound {c : ℝ × HeatCircle → ℝ} {r C : ℝ}
    (hc : Measurable c) (hr : 0 < r) (hr1 : r ≤ 1) (hC : 0 ≤ C)
    (hbound : ∀ s ∈ Ioo 0 r, ∀ y, |c (s, y)| ≤ C) (x : HeatCircle) :
    IntervalIntegrable (varianceDensity c r x) volume 0 r ∧
      |varianceMap c r x| ≤ 2 * (1 + heatConstant) * C * r ^ (1 / 2 : ℝ) := by
  have hHC : 0 ≤ 1 + heatConstant := by linarith [heatConstant_pos]
  have hp : IntervalIntegrable (fun s : ℝ => (r - s) ^ (-(1 / 2 : ℝ))) volume 0 r := by
    have hi : IntervalIntegrable (fun s : ℝ => s ^ (-(1 / 2 : ℝ))) volume 0 r :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    simpa using (hi.comp_sub_left r).symm
  have hb : ∀ s ∈ Ioo 0 r, |varianceDensity c r x s| ≤
      (C * (1 + heatConstant)) * (r - s) ^ (-(1 / 2 : ℝ)) := by
    intro s hs
    have hv := varianceDensity_bound hc hC hs.2 (hbound s hs) x
    have hm := mul_le_mul_of_nonneg_left (heat_mass_small_time
      (show 0 < r - s by linarith [hs.2]) (show r - s ≤ 1 by linarith [hs.1]) x) hC
    exact hv.trans (by simpa only [mul_assoc] using hm)
  have hi : IntervalIntegrable (varianceDensity c r x) volume 0 r := by
    apply (hp.const_mul (C * (1 + heatConstant))).mono_fun'
    · exact (varianceDensity_measurable hc r x).aestronglyMeasurable
    · rw [uIoc_of_le hr.le]
      filter_upwards [ae_restrict_mem measurableSet_Ioc,
        ae_restrict_of_ae (volume.ae_ne r)] with s hs hsr
      rw [Real.norm_eq_abs]
      exact hb s ⟨hs.1, lt_of_le_of_ne hs.2 hsr⟩
  refine ⟨hi, ?_⟩
  unfold varianceMap
  rw [← Real.norm_eq_abs, intervalIntegral.integral_of_le hr.le]
  calc
    _ ≤ ∫ s in Ioc (0 : ℝ) r, ‖varianceDensity c r x s‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ s in Ioc (0 : ℝ) r, (C * (1 + heatConstant)) * (r - s) ^ (-(1 / 2 : ℝ)) := by
      apply integral_mono_ae hi.1.norm (hp.const_mul (C * (1 + heatConstant))).1
      filter_upwards [ae_restrict_mem measurableSet_Ioc,
        ae_restrict_of_ae (volume.ae_ne r)] with s hs hsr
      rw [Real.norm_eq_abs]
      exact hb s ⟨hs.1, lt_of_le_of_ne hs.2 hsr⟩
    _ = _ := by
      rw [← intervalIntegral.integral_of_le hr.le, intervalIntegral.integral_const_mul,
        heat_mass_time_integral hr]
      ring

theorem varianceMap_sub {c d : ℝ × HeatCircle → ℝ} {r M : ℝ}
    (hc : Measurable c) (hd : Measurable d) (hr : 0 < r) (hr1 : r ≤ 1) (hM : 0 ≤ M)
    (hcM : ∀ s ∈ Ioo 0 r, ∀ y, |c (s, y)| ≤ M)
    (hdM : ∀ s ∈ Ioo 0 r, ∀ y, |d (s, y)| ≤ M) (x : HeatCircle) :
    varianceMap (c - d) r x = varianceMap c r x - varianceMap d r x := by
  have hiC := (varianceMap_bound hc hr hr1 hM hcM x).1
  have hiD := (varianceMap_bound hd hr hr1 hM hdM x).1
  unfold varianceMap
  rw [← intervalIntegral.integral_sub hiC hiD]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le hr.le]
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (volume.ae_ne r)] with s hs hsr
  have hs' : s ∈ Ioo 0 r := ⟨hs.1, lt_of_le_of_ne hs.2 hsr⟩
  unfold varianceDensity
  simp only [Pi.sub_apply, mul_sub]
  exact integral_sub (varianceDensity_integrable hc hM hs'.2 (hcM s hs') x)
    (varianceDensity_integrable hd hM hs'.2 (hdM s hs') x)

/-- The concrete covariance map is `O(√r)` Lipschitz on its bounded measurable
profile domain, uniformly in the original physical center. -/
theorem varianceMap_lipschitz {c d : ℝ × HeatCircle → ℝ} {r M D : ℝ}
    (hc : Measurable c) (hd : Measurable d) (hr : 0 < r) (hr1 : r ≤ 1)
    (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hcM : ∀ s ∈ Ioo 0 r, ∀ y, |c (s, y)| ≤ M)
    (hdM : ∀ s ∈ Ioo 0 r, ∀ y, |d (s, y)| ≤ M)
    (hcd : ∀ s ∈ Ioo 0 r, ∀ y, |c (s, y) - d (s, y)| ≤ D) (x : HeatCircle) :
    |varianceMap c r x - varianceMap d r x| ≤
      2 * (1 + heatConstant) * D * r ^ (1 / 2 : ℝ) := by
  rw [← varianceMap_sub hc hd hr hr1 hM hcM hdM]
  exact (varianceMap_bound (hc.sub hd) hr hr1 hD hcd x).2

def lowerConstant : ℝ := HeatTrace.fractionalGaussianIntegral 0 * (2 : ℝ) ^ (-(1 / 2 : ℝ))

def upperConstant : ℝ := 2 * (1 + heatConstant)

theorem lowerConstant_pos : 0 < lowerConstant := by
  exact mul_pos (HeatTrace.fractionalGaussianIntegral_pos (by norm_num))
    (Real.rpow_pos_of_pos (by norm_num) _)

theorem upperConstant_pos : 0 < upperConstant := by
  unfold upperConstant
  linarith [heatConstant_pos]

/-- Elliptic scalar profiles produce the actual covariance scale `√r`, uniformly
in the original physical center. -/
theorem varianceMap_elliptic {c : ℝ × HeatCircle → ℝ} {r m M : ℝ}
    (hc : Measurable c) (hr : 0 < r) (hr1 : r ≤ 1) (hm : 0 ≤ m) (hM : 0 ≤ M)
    (hlower : ∀ s ∈ Ioo 0 r, ∀ y, m ≤ c (s, y))
    (hupper : ∀ s ∈ Ioo 0 r, ∀ y, c (s, y) ≤ M) (x : HeatCircle) :
    lowerConstant * m * r ^ (1 / 2 : ℝ) ≤ varianceMap c r x ∧
      varianceMap c r x ≤ upperConstant * M * r ^ (1 / 2 : ℝ) := by
  have habs : ∀ s ∈ Ioo 0 r, ∀ y, |c (s, y)| ≤ M := by
    intro s hs y
    rw [abs_of_nonneg (hm.trans (hlower s hs y))]
    exact hupper s hs y
  have hv := varianceMap_bound hc hr hr1 hM habs x
  have hG : 0 < HeatTrace.fractionalGaussianIntegral 0 :=
    HeatTrace.fractionalGaussianIntegral_pos (by norm_num)
  have hd : ∀ s ∈ Ioo 0 r,
      HeatTrace.fractionalGaussianIntegral 0 * (2 * r) ^ (-(1 / 2 : ℝ)) * m ≤ varianceDensity c r x s := by
    intro s hs
    have hs0 : 0 < r - s := by linarith [hs.2]
    have hp : (2 * r) ^ (-(1 / 2 : ℝ)) ≤ (2 * (r - s)) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith [hs.1]) (by norm_num)
    have hh := (mul_le_mul_of_nonneg_left hp hG.le).trans (circleHeat_norm_sq_lower hs0 x)
    have hsint := heatPhysical_square_integrable hs0 x
    have hrow := varianceDensity_integrable hc hM hs.2 (habs s hs) x
    have hmrow : m * ‖circleHeat (r - s) x‖ ^ 2 ≤ varianceDensity c r x s := by
      unfold varianceDensity
      rw [← heatPhysical_square_mass hs0 x, ← integral_const_mul]
      apply integral_mono (hsint.const_mul m) hrow
      intro y
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hlower s hs y) (sq_nonneg ‖heatPhysical (r - s) x y‖)
    have hmhh : HeatTrace.fractionalGaussianIntegral 0 * (2 * r) ^ (-(1 / 2 : ℝ)) * m ≤
        m * ‖circleHeat (r - s) x‖ ^ 2 := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh hm
    exact hmhh.trans hmrow
  have hlow : HeatTrace.fractionalGaussianIntegral 0 * (2 * r) ^ (-(1 / 2 : ℝ)) * m * r ≤
      varianceMap c r x := by
    unfold varianceMap
    have he := intervalIntegral.integral_mono_on_of_le_Ioo hr.le
      (intervalIntegrable_const : IntervalIntegrable
        (fun _ : ℝ => HeatTrace.fractionalGaussianIntegral 0 * (2 * r) ^ (-(1 / 2 : ℝ)) * m) volume 0 r) hv.1 hd
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] using he
  have halg : HeatTrace.fractionalGaussianIntegral 0 * (2 * r) ^ (-(1 / 2 : ℝ)) * m * r =
      lowerConstant * m * r ^ (1 / 2 : ℝ) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr.le]
    calc
      _ = (HeatTrace.fractionalGaussianIntegral 0 * (2 : ℝ) ^ (-(1 / 2 : ℝ))) * m *
          (r ^ (-(1 / 2 : ℝ)) * r ^ (1 : ℝ)) := by rw [Real.rpow_one]; ring
      _ = _ := by rw [← Real.rpow_add hr, show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring]; rfl
  refine ⟨by rwa [halg] at hlow, ?_⟩
  exact (le_abs_self _).trans (by simpa only [upperConstant, mul_assoc] using hv.2)

theorem heatPhysical_joint_measurable :
    Measurable (fun p : (ℝ × HeatCircle) × HeatCircle => heatPhysical p.1.1 p.1.2 p.2) := by
  unfold heatPhysical heatCrossKernel
  apply Measurable.tsum
  intro n
  have he : Measurable (fun p : (ℝ × HeatCircle) × HeatCircle =>
      (Real.exp (-p.1.1 * (n : ℝ) ^ 2) : ℂ)) := by fun_prop
  exact (he.mul ((fourier n).continuous.measurable.comp measurable_snd)).mul
    ((fourier (-n)).continuous.measurable.comp measurable_fst.snd)

theorem varianceDensity_joint_measurable {c : ℝ × HeatCircle → ℝ} (hc : Measurable c) :
    Measurable (fun p : (ℝ × HeatCircle) × ℝ => varianceDensity c p.1.1 p.1.2 p.2) := by
  have hk : Measurable (fun p : ((ℝ × HeatCircle) × ℝ) × HeatCircle =>
      heatPhysical (p.1.1.1 - p.1.2) p.1.1.2 p.2) :=
    heatPhysical_joint_measurable.comp
      ((((measurable_fst.fst.fst).sub measurable_fst.snd).prodMk measurable_fst.fst.snd).prodMk measurable_snd)
  have hc' : Measurable (fun p : ((ℝ × HeatCircle) × ℝ) × HeatCircle => c (p.1.2, p.2)) :=
    hc.comp (measurable_fst.snd.prodMk measurable_snd)
  exact (((hk.norm.pow_const (2 : ℕ)).mul hc').stronglyMeasurable.integral_prod_right).measurable

/-- A globally measurable extension of the actual covariance map from nonnegative times. -/
def positiveVarianceMap (c : ℝ × HeatCircle → ℝ) (p : ℝ × HeatCircle) : ℝ :=
  ∫ s : ℝ, if 0 < s ∧ s ≤ p.1 then varianceDensity c p.1 p.2 s else 0

theorem positiveVarianceMap_measurable {c : ℝ × HeatCircle → ℝ} (hc : Measurable c) :
    Measurable (positiveVarianceMap c) := by
  classical
  have hset : MeasurableSet {p : (ℝ × HeatCircle) × ℝ | 0 < p.2 ∧ p.2 ≤ p.1.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst.fst)
  have hm : Measurable (fun p : (ℝ × HeatCircle) × ℝ =>
      if 0 < p.2 ∧ p.2 ≤ p.1.1 then varianceDensity c p.1.1 p.1.2 p.2 else 0) :=
    (varianceDensity_joint_measurable hc).ite hset measurable_const
  exact hm.stronglyMeasurable.integral_prod_right.measurable

theorem positiveVarianceMap_eq {c : ℝ × HeatCircle → ℝ} {r : ℝ} (hr : 0 ≤ r) (x : HeatCircle) :
    positiveVarianceMap c (r, x) = varianceMap c r x := by
  unfold positiveVarianceMap varianceMap
  rw [intervalIntegral.integral_of_le hr, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with s
  by_cases hs : 0 < s ∧ s ≤ r
  · rw [ite_eq_left hs, Set.indicator_of_mem (s := Ioc 0 r) hs]
  · rw [ite_eq_right hs, Set.indicator_of_notMem (s := Ioc 0 r) hs]

end SHE.ProfileVariance
