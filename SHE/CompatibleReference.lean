module

public import SHE.PhysicalProfile

@[expose] public section
set_option autoImplicit false

/-! Actual scalar reference heat-row energy for the pointwise-square-root
coupling. The manuscript's nonlocal common-Haar factor is a separate coupling. -/
noncomputable section
namespace SHE.CompatibleReference
open Set MeasureTheory AddCircle StoppedFourier ProfileVariance GaussianProfile ProfileL2 ProfileStability PhysicalProfile

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

def rootConstant (ell : ℝ) : ℝ := (2 * Real.sqrt ell)⁻¹

theorem rootConstant_nonneg (ell : ℝ) : 0 ≤ rootConstant ell := by
  exact inv_nonneg.mpr (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))

theorem scalar_sqrt_lipschitz {ell x y : ℝ} (hell : 0 < ell) (hx : ell ≤ x) (hy : ell ≤ y) :
    |Real.sqrt x - Real.sqrt y| ≤ rootConstant ell * |x - y| := by
  have hx0 : 0 ≤ x := hell.le.trans hx
  have hy0 : 0 ≤ y := hell.le.trans hy
  have hxl : Real.sqrt ell ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
  have hyl : Real.sqrt ell ≤ Real.sqrt y := Real.sqrt_le_sqrt hy
  have hpos : 0 < 2 * Real.sqrt ell := mul_pos (by norm_num) (Real.sqrt_pos.mpr hell)
  have he : (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y) = x - y := by
    nlinarith [Real.sq_sqrt hx0, Real.sq_sqrt hy0]
  have habs : |Real.sqrt x - Real.sqrt y| * (Real.sqrt x + Real.sqrt y) = |x - y| := by
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)), ← abs_mul, he]
  have hb : |Real.sqrt x - Real.sqrt y| ≤ |x - y| / (2 * Real.sqrt ell) := by
    apply (le_div_iff₀ hpos).mpr
    calc
      _ ≤ |Real.sqrt x - Real.sqrt y| * (Real.sqrt x + Real.sqrt y) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ = _ := habs
  simpa only [rootConstant, div_eq_mul_inv, mul_comm] using hb

def rootDifference (c d : ℝ × HeatCircle → ℝ) (p : ℝ × HeatCircle) : ℝ :=
  (Real.sqrt (c p) - Real.sqrt (d p)) ^ 2

theorem rootDifference_measurable {c d : ℝ × HeatCircle → ℝ}
    (hc : Measurable c) (hd : Measurable d) : Measurable (rootDifference c d) :=
  (hc.sqrt.sub hd.sqrt).pow_const (2 : ℕ)

theorem rootDifference_nonneg (c d : ℝ × HeatCircle → ℝ) (p : ℝ × HeatCircle) :
    0 ≤ rootDifference c d p := sq_nonneg _

theorem rootDifference_bound {c d : ℝ × HeatCircle → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hc : ∀ p, 0 ≤ c p ∧ c p ≤ M) (hd : ∀ p, 0 ≤ d p ∧ d p ≤ M)
    (p : ℝ × HeatCircle) : |rootDifference c d p| ≤ 4 * M := by
  have hcs := Real.sqrt_le_sqrt (hc p).2
  have hds := Real.sqrt_le_sqrt (hd p).2
  have hc0 := Real.sqrt_nonneg (c p)
  have hd0 := Real.sqrt_nonneg (d p)
  rw [abs_of_nonneg (rootDifference_nonneg _ _ _)]
  unfold rootDifference
  have he : |Real.sqrt (c p) - Real.sqrt (d p)| ≤ 2 * Real.sqrt M := by
    rw [abs_le]
    constructor <;> linarith [Real.sqrt_nonneg M]
  have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * Real.sqrt M)).mpr he
  rw [sq_abs, mul_pow, Real.sq_sqrt hM] at hs
  norm_num at hs ⊢
  exact hs

theorem rootDifference_pointwise {c d : ℝ × HeatCircle → ℝ} {ell : ℝ}
    (hell : 0 < ell) (hc : ∀ p, ell ≤ c p) (hd : ∀ p, ell ≤ d p) (p : ℝ × HeatCircle) :
    rootDifference c d p ≤ rootConstant ell ^ 2 * (c p - d p) ^ 2 := by
  have he := scalar_sqrt_lipschitz hell (hc p) (hd p)
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (rootConstant_nonneg ell) (abs_nonneg _))).mpr he
  simpa only [sq_abs, mul_pow, rootDifference] using hs

/-- Integrating the genuine squared heat kernel over the output center gives
its exact mass times the spatial input integral. -/
theorem heat_square_mass_action {t C : ℝ} {f : HeatCircle → ℝ}
    (ht : 0 < t) (hf : Measurable f) (_hC : 0 ≤ C) (hfb : ∀ y, |f y| ≤ C) :
    (∫ x, ∫ y, ‖heatPhysical t x y‖ ^ 2 * f y ∂haarAddCircle ∂haarAddCircle) =
      ‖circleHeat t (0 : HeatCircle)‖ ^ 2 * ∫ y, f y ∂haarAddCircle := by
  have hk : Measurable (fun p : HeatCircle × HeatCircle => ‖heatPhysical t p.1 p.2‖ ^ 2) :=
    (heatPhysical_joint_measurable.comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)).norm.pow_const (2 : ℕ)
  have hi : Integrable (fun p : HeatCircle × HeatCircle => ‖heatPhysical t p.1 p.2‖ ^ 2 * f p.2)
      (haarAddCircle.prod haarAddCircle) := by
    apply (integrable_const (‖circleHeat (t / 2) (0 : HeatCircle)‖ ^ 4 * C)).mono'
    · exact (hk.mul (hf.comp measurable_snd)).aestronglyMeasurable
    · filter_upwards with p
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul (heatPhysical_square_uniform_bound ht _ _) (hfb _) (abs_nonneg _) (by positivity)
  rw [integral_integral_swap hi]
  have hm (y : HeatCircle) : (∫ x, ‖heatPhysical t x y‖ ^ 2 ∂haarAddCircle) =
      ‖circleHeat t (0 : HeatCircle)‖ ^ 2 := by
    simp_rw [heatPhysical_norm_symm ht _ y]
    rw [heatPhysical_square_mass ht, circleHeat_norm_sq_center t y 0]
  simp_rw [integral_mul_const, hm]
  rw [integral_const_mul]

theorem rootDifference_spatial_integral_le {c d : ℝ × HeatCircle → ℝ} {ell M : ℝ}
    (hc : Measurable c) (hd : Measurable d) (hell : 0 < ell) (hM : 0 ≤ M)
    (hcb : ∀ p, ell ≤ c p ∧ c p ≤ M) (hdb : ∀ p, ell ≤ d p ∧ d p ≤ M) (s : ℝ) :
    (∫ y, rootDifference c d (s, y) ∂haarAddCircle) ≤
      rootConstant ell ^ 2 * normTwo haarAddCircle (fun y => c (s, y) - d (s, y)) ^ 2 := by
  have hr := rootDifference_measurable hc hd
  have hrb : ∀ y, |rootDifference c d (s, y)| ≤ 4 * M :=
    fun y => rootDifference_bound hM (fun p => ⟨hell.le.trans (hcb p).1, (hcb p).2⟩)
      (fun p => ⟨hell.le.trans (hdb p).1, (hdb p).2⟩) (s, y)
  have hri := (bounded_memLp (μ := haarAddCircle)
    (hr.comp (measurable_const.prodMk measurable_id)) hrb).integrable (by norm_num)
  have hdi : MemLp (fun y => c (s, y) - d (s, y)) 2 haarAddCircle := by
    apply bounded_memLp (C := 2 * M) ((hc.sub hd).comp (measurable_const.prodMk measurable_id))
    intro y
    change |c (s, y) - d (s, y)| ≤ 2 * M
    rw [abs_le]
    constructor <;> linarith [(hcb (s, y)).1, (hcb (s, y)).2, (hdb (s, y)).1, (hdb (s, y)).2]
  rw [normTwo_sq, ← integral_const_mul]
  apply integral_mono hri (hdi.integrable_sq.const_mul _)
  intro y
  exact rootDifference_pointwise hell (fun p => (hcb p).1) (fun p => (hdb p).1) (s, y)

/-- The actual spatial Hilbert--Schmidt row density for the compatible scalar
reference coefficient difference `sqrt c - sqrt d`. -/
def rowEnergy (c d : ℝ × HeatCircle → ℝ) (r s : ℝ) : ℝ :=
  ∫ x : HeatCircle, varianceDensity (rootDifference c d) r x s ∂haarAddCircle

def noiseRowConstant (ell : ℝ) : ℝ := (1 + heatConstant) * rootConstant ell ^ 2

theorem noiseRowConstant_nonneg (ell : ℝ) : 0 ≤ noiseRowConstant ell :=
  mul_nonneg (by linarith [heatConstant_pos]) (sq_nonneg _)

theorem rowEnergy_measurable {c d : ℝ × HeatCircle → ℝ}
    (hc : Measurable c) (hd : Measurable d) (r : ℝ) : Measurable (rowEnergy c d r) := by
  have hmap : Measurable (fun p : ℝ × HeatCircle => ((r, p.2), p.1)) :=
    (measurable_const.prodMk measurable_snd).prodMk measurable_fst
  have hm := (varianceDensity_joint_measurable (rootDifference_measurable hc hd)).comp hmap
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem rowEnergy_nonneg (c d : ℝ × HeatCircle → ℝ) (r s : ℝ) :
    0 ≤ rowEnergy c d r s :=
  integral_nonneg (fun _ => integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))

/-- The concrete physical heat row has the squared-profile energy bound.
No Hilbert--Schmidt estimate or stochastic isometry is assumed. -/
theorem rowEnergy_bound {c d : ℝ × HeatCircle → ℝ} {ell M r s : ℝ}
    (hc : Measurable c) (hd : Measurable d) (hell : 0 < ell) (hM : 0 ≤ M)
    (hcb : ∀ p, ell ≤ c p ∧ c p ≤ M) (hdb : ∀ p, ell ≤ d p ∧ d p ≤ M)
    (hs : s < r) (hrs : r - s ≤ 1) :
    rowEnergy c d r s ≤ noiseRowConstant ell * ((r - s) ^ (-(1 / 2 : ℝ)) *
      normTwo haarAddCircle (fun y => c (s, y) - d (s, y)) ^ 2) := by
  have hb (y : HeatCircle) : |rootDifference c d (s, y)| ≤ 4 * M :=
    rootDifference_bound hM (fun p => ⟨hell.le.trans (hcb p).1, (hcb p).2⟩)
      (fun p => ⟨hell.le.trans (hdb p).1, (hdb p).2⟩) (s, y)
  have hmass := heat_square_mass_action (sub_pos.mpr hs)
    ((rootDifference_measurable hc hd).comp (measurable_const.prodMk measurable_id))
    (by positivity : 0 ≤ 4 * M) hb
  change rowEnergy c d r s = _ at hmass
  rw [hmass]
  calc
    _ ≤ ‖circleHeat (r - s) (0 : HeatCircle)‖ ^ 2 *
        (rootConstant ell ^ 2 * normTwo haarAddCircle (fun y => c (s, y) - d (s, y)) ^ 2) :=
      mul_le_mul_of_nonneg_left (rootDifference_spatial_integral_le hc hd hell hM hcb hdb s) (sq_nonneg _)
    _ ≤ ((1 + heatConstant) * (r - s) ^ (-(1 / 2 : ℝ))) *
        (rootConstant ell ^ 2 * normTwo haarAddCircle (fun y => c (s, y) - d (s, y)) ^ 2) :=
      mul_le_mul_of_nonneg_right (heat_mass_small_time (sub_pos.mpr hs) hrs 0) (by positivity)
    _ = _ := by unfold noiseRowConstant; ring

/-- The actual compatible-reference row is integrable in time and gains
`h^(β/2)` from the proved profile stability scale. -/
theorem rowEnergy_time_bound {c d : ℝ × HeatCircle → ℝ} {ell M β h P D : ℝ}
    (hc : Measurable c) (hd : Measurable d) (hell : 0 < ell) (hM : 0 ≤ M)
    (hcb : ∀ p, ell ≤ c p ∧ c p ≤ M) (hdb : ∀ p, ell ≤ d p ∧ d p ≤ M)
    (hβ : -1 < β) (hh : 0 < h) (hh1 : h ≤ 1) (hP : 0 ≤ P) (hD : 0 ≤ D)
    (hprofile : ∀ s ∈ Ioo 0 h, normTwo haarAddCircle (fun y => c (s, y) - d (s, y)) ≤
      P * D * s ^ ((β - 1) / 4)) :
    IntervalIntegrable (rowEnergy c d h) volume 0 h ∧
      (∫ s in (0 : ℝ)..h, rowEnergy c d h s) ≤
        noiseRowConstant ell * P ^ 2 * ProfileVolterra.powerConstant ((β - 1) / 2) *
          h ^ (β / 2) * D ^ 2 := by
  let f : ℝ → ℝ := fun s => normTwo haarAddCircle (fun y => c (s, y) - d (s, y))
  have hf : Measurable f := spatial_normTwo_measurable (hc.sub hd)
  have hconv := ProfileVolterra.squared_profile_convolution_bound hβ hh hP hD hf
    (fun _ _ => normTwo_nonneg _ _) hprofile
  have hrow : ∀ s ∈ Ioo 0 h, rowEnergy c d h s ≤
      noiseRowConstant ell * ((h - s) ^ (-(1 / 2 : ℝ)) * f s ^ 2) := by
    intro s hs
    exact rowEnergy_bound hc hd hell hM hcb hdb hs.2 (by linarith [hs.1])
  have hi : IntervalIntegrable (rowEnergy c d h) volume 0 h := by
    apply (hconv.1.const_mul (noiseRowConstant ell)).mono_fun'
    · exact (rowEnergy_measurable hc hd h).aestronglyMeasurable
    · rw [uIoc_of_le hh.le]
      filter_upwards [ae_restrict_mem measurableSet_Ioc,
        ae_restrict_of_ae (volume.ae_ne h)] with s hs hsh
      rw [Real.norm_eq_abs, abs_of_nonneg (rowEnergy_nonneg _ _ _ _)]
      exact hrow s ⟨hs.1, lt_of_le_of_ne hs.2 hsh⟩
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ s in (0 : ℝ)..h, noiseRowConstant ell * ((h - s) ^ (-(1 / 2 : ℝ)) * f s ^ 2) :=
      intervalIntegral.integral_mono_on_of_le_Ioo hh.le hi
        (hconv.1.const_mul (noiseRowConstant ell)) hrow
    _ = noiseRowConstant ell * (∫ s in (0 : ℝ)..h, (h - s) ^ (-(1 / 2 : ℝ)) * f s ^ 2) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ noiseRowConstant ell * (P ^ 2 * D ^ 2 *
        ProfileVolterra.powerConstant ((β - 1) / 2) * h ^ (β / 2)) :=
      mul_le_mul_of_nonneg_left hconv.2 (noiseRowConstant_nonneg ell)
    _ = _ := by ring

def referenceConstant (ell H β : ℝ) : ℝ :=
  4 * noiseRowConstant ell * meanConstant ell H β ^ 2 * ProfileVolterra.powerConstant ((β - 1) / 2)

theorem referenceConstant_nonneg {ell H β : ℝ} (hβ : -1 < β) :
    0 ≤ referenceConstant ell H β :=
  mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (noiseRowConstant_nonneg _)) (sq_nonneg _))
    (ProfileVolterra.powerConstant_pos (by linarith)).le

/-- The full deterministic reference variance estimate for the pointwise
square-root coupling, with actual heat rows and actual one-input profiles. -/
theorem physical_profile_reference_energy_bound {a : ℝ → ℝ} {c d : ℝ × HeatCircle → ℝ}
    {ell M Ua H β h : ℝ} (u v : CircleL2)
    (ha : Measurable a) (hc : Measurable c) (hd : Measurable d)
    (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hh : 0 < h) (hh1 : h ≤ 1) (haB : ∀ z, |a z| ≤ Ua)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hcb : ∀ p, ell ≤ c p ∧ c p ≤ M) (hdb : ∀ p, ell ≤ d p ∧ d p ≤ M)
    (hsmall : memoryConstant ell H β * ProfileVolterra.powerConstant ((β - 1) / 4) *
      h ^ (β / 4) ≤ 1 / 2)
    (hcf : ∀ r ∈ Ioc 0 h, ∀ x, c (r, x) = profileUpdate a (physicalHeatMean u) c r x)
    (hdf : ∀ r ∈ Ioc 0 h, ∀ x, d (r, x) = profileUpdate a (physicalHeatMean v) d r x) :
    IntervalIntegrable (rowEnergy c d h) volume 0 h ∧
      (∫ s in (0 : ℝ)..h, rowEnergy c d h s) ≤
        referenceConstant ell H β * h ^ (β / 2) * ‖u - v‖ ^ 2 := by
  have hstable := physical_profile_l2_stability u v ha hc hd hell hM hH hβ hβ1 hh hh1
    haB hholder hcb hdb hsmall hcf hdf
  have he := rowEnergy_time_bound (P := 2 * meanConstant ell H β) (D := ‖u - v‖)
    hc hd hell hM hcb hdb (by linarith : -1 < β) hh hh1
    (mul_nonneg (by norm_num) (meanConstant_nonneg (β := β) hell.le hH)) (norm_nonneg (u - v))
    (fun s hs => by
      have hh := hstable s ⟨hs.1, hs.2.le⟩
      convert hh using 1
      ring)
  refine ⟨he.1, ?_⟩
  convert he.2 using 1
  unfold referenceConstant
  ring

/-- Actual pointwise-square-root reference L² stability after the standard centered
stochastic-integral isometry has been supplied. Its row density is the
concrete physical heat-square/square-root-profile integral defined above;
neither profile stability nor a heat-row bound is an input. -/
theorem physical_reference_stability_from_isometry
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Z : Ω → CircleL2} (hZ : MemLp Z 2 μ) (hcenter : (∫ ω, Z ω ∂μ) = 0)
    {a : ℝ → ℝ} {c d : ℝ × HeatCircle → ℝ} {ell M Ua H β h : ℝ} (u v : CircleL2)
    (ha : Measurable a) (hc : Measurable c) (hd : Measurable d)
    (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hh : 0 < h) (hh1 : h ≤ 1) (haB : ∀ z, |a z| ≤ Ua)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hcb : ∀ p, ell ≤ c p ∧ c p ≤ M) (hdb : ∀ p, ell ≤ d p ∧ d p ≤ M)
    (hsmall : memoryConstant ell H β * ProfileVolterra.powerConstant ((β - 1) / 4) *
      h ^ (β / 4) ≤ 1 / 2)
    (hcf : ∀ r ∈ Ioc 0 h, ∀ x, c (r, x) = profileUpdate a (physicalHeatMean u) c r x)
    (hdf : ∀ r ∈ Ioc 0 h, ∀ x, d (r, x) = profileUpdate a (physicalHeatMean v) d r x)
    (hisometry : (∫ ω, ‖Z ω‖ ^ 2 ∂μ) = ∫ s in (0 : ℝ)..h, rowEnergy c d h s) :
    (∫ ω, ‖Z ω‖ ^ 2 ∂μ) ≤
      referenceConstant ell H β * h ^ (β / 2) * ‖u - v‖ ^ 2 ∧
    (∫ ω, ‖circleHeatOperator h hh.le (u - v) + Z ω‖ ^ 2 ∂μ) ≤
      (1 + referenceConstant ell H β) * ‖u - v‖ ^ 2 := by
  have hrow := physical_profile_reference_energy_bound u v ha hc hd hell hM hH hβ hβ1 hh hh1
    haB hholder hcb hdb hsmall hcf hdf
  have hnoise : (∫ ω, ‖Z ω‖ ^ 2 ∂μ) ≤
      referenceConstant ell H β * h ^ (β / 2) * ‖u - v‖ ^ 2 := by
    rw [hisometry]
    exact hrow.2
  refine ⟨hnoise, ?_⟩
  exact ProfileVolterra.compatible_reference_total_bound μ hZ hcenter
    (circleHeatOperator h hh.le (u - v)) hβ.le hh hh1 (norm_nonneg _)
    (referenceConstant_nonneg (ell := ell) (H := H) (by linarith : -1 < β))
    (circleHeatOperator_norm_le h hh.le (u - v)) hnoise

end SHE.CompatibleReference
