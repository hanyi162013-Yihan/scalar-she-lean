module

public import SHE.RootConvolution
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section
set_option autoImplicit false

/-! Weighted Volterra absorption for the actual bounded measurable profile inequality. -/
noncomputable section
namespace SHE.ProfileVolterra
open Set MeasureTheory

def powerConstant (a : ℝ) : ℝ := 2 * (1 / (a + 1) + 2)

theorem powerConstant_pos {a : ℝ} (ha : -1 < a) : 0 < powerConstant a := by
  unfold powerConstant
  have hh : 0 < a + 1 := by linarith
  positivity

/-- The weakly singular convolution is genuinely integrable and bounded, rather
than being supplied as an assumed operator norm. -/
theorem singular_convolution_bound {a t S : ℝ} {f : ℝ → ℝ}
    (ha : -1 < a) (ht : 0 < t) (hS : 0 ≤ S) (hf : Measurable f)
    (hf0 : ∀ u ∈ Ioo 0 t, 0 ≤ f u) (hfb : ∀ u ∈ Ioo 0 t, f u ≤ S * u ^ a) :
    IntervalIntegrable (fun u => (t - u) ^ (-(1 / 2 : ℝ)) * f u) volume 0 t ∧
    (∫ u in (0 : ℝ)..t, (t - u) ^ (-(1 / 2 : ℝ)) * f u) ≤
      S * powerConstant a * t ^ (a + 1 / 2) := by
  have hp : IntervalIntegrable (fun u => u ^ a * (t - u) ^ (-(1 / 2 : ℝ))) volume 0 t := by
    simpa only [show a + 1 - 1 = a by ring, show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by ring]
      using positive_power_pair_intervalIntegrable (show 0 < a + 1 by linarith)
        (show (0 : ℝ) < 1 / 2 by norm_num) ht.le
  have hb : ∀ u ∈ Ioo 0 t, (t - u) ^ (-(1 / 2 : ℝ)) * f u ≤
      S * (u ^ a * (t - u) ^ (-(1 / 2 : ℝ))) := by
    intro u hu
    have he := mul_le_mul_of_nonneg_left (hfb u hu)
      (Real.rpow_nonneg (by linarith [hu.2] : 0 ≤ t - u) (-(1 / 2 : ℝ)))
    nlinarith
  have hi : IntervalIntegrable (fun u => (t - u) ^ (-(1 / 2 : ℝ)) * f u) volume 0 t := by
    apply (hp.const_mul S).mono_fun'
    · exact (((real_rpow_measurable _).comp (measurable_const.sub measurable_id)).mul hf).aestronglyMeasurable
    · rw [uIoc_of_le ht.le]
      filter_upwards [ae_restrict_mem measurableSet_Ioc,
        ae_restrict_of_ae (volume.ae_ne t)] with u hu hut
      have hu' : u ∈ Ioo 0 t := ⟨hu.1, lt_of_le_of_ne hu.2 hut⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (Real.rpow_nonneg (by linarith [hu.2] : 0 ≤ t - u) _) (hf0 u hu'))]
      exact hb u hu'
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ u in (0 : ℝ)..t, S * (u ^ a * (t - u) ^ (-(1 / 2 : ℝ))) :=
      intervalIntegral.integral_mono_on_of_le_Ioo ht.le hi (hp.const_mul S) hb
    _ = S * (∫ u in (0 : ℝ)..t, u ^ a * (t - u) ^ (-(1 / 2 : ℝ))) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ S * (powerConstant a * t ^ (a + 1 / 2)) := by
      apply mul_le_mul_of_nonneg_left _ hS
      have he := positive_power_convolution_le (show 0 < a + 1 by linarith)
        (show (0 : ℝ) < 1 / 2 by norm_num) ht
      simpa only [show a + 1 - 1 = a by ring, show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by ring,
        show a + 1 + 1 / 2 - 1 = a + 1 / 2 by ring, one_div_div, div_one, powerConstant]
        using he
    _ = _ := by ring

def weightedValues (f : ℝ → ℝ) (a h : ℝ) : Set ℝ :=
  (fun t => t ^ (-a) * f t) '' Ioc 0 h

def weightedSup (f : ℝ → ℝ) (a h : ℝ) : ℝ := sSup (weightedValues f a h)

theorem weightedValues_nonempty {f : ℝ → ℝ} {a h : ℝ} (hh : 0 < h) :
    (weightedValues f a h).Nonempty := ⟨h ^ (-a) * f h, h, ⟨hh, le_rfl⟩, rfl⟩

/-- Bounded profiles give a finite weighted supremum for the singular stability exponent. -/
theorem weightedValues_bddAbove {f : ℝ → ℝ} {a h M : ℝ}
    (ha : a ≤ 0) (hh : h ≤ 1) (_hM : 0 ≤ M)
    (hf0 : ∀ t ∈ Ioc 0 h, 0 ≤ f t) (hfb : ∀ t ∈ Ioc 0 h, f t ≤ M) :
    BddAbove (weightedValues f a h) := by
  refine ⟨M, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have hw : t ^ (-a) ≤ 1 := Real.rpow_le_one ht.1.le (ht.2.trans hh) (by linarith)
  exact (mul_le_mul_of_nonneg_right hw (hf0 t ht)).trans (by simpa only [one_mul] using hfb t ht)

theorem weightedSup_nonneg {f : ℝ → ℝ} {a h : ℝ} (hh : 0 < h)
    (hb : BddAbove (weightedValues f a h)) (hf0 : ∀ t ∈ Ioc 0 h, 0 ≤ f t) :
    0 ≤ weightedSup f a h := by
  apply (mul_nonneg (Real.rpow_nonneg hh.le _) (hf0 h ⟨hh, le_rfl⟩)).trans
  exact le_csSup hb ⟨h, ⟨hh, le_rfl⟩, rfl⟩

theorem le_weightedSup_mul {f : ℝ → ℝ} {a h t : ℝ}
    (hb : BddAbove (weightedValues f a h)) (ht : t ∈ Ioc 0 h) :
    f t ≤ weightedSup f a h * t ^ a := by
  have he : t ^ (-a) * f t ≤ weightedSup f a h := le_csSup hb ⟨t, ht, rfl⟩
  have hh := mul_le_mul_of_nonneg_right he (Real.rpow_nonneg ht.1.le a)
  have hc : t ^ (-a) * t ^ a = 1 := by rw [← Real.rpow_add ht.1, neg_add_cancel, Real.rpow_zero]
  have hr : t ^ (-a) * f t * t ^ a = f t := by
    calc
      _ = f t * (t ^ (-a) * t ^ a) := by ring
      _ = _ := by rw [hc, mul_one]
  rwa [hr] at hh

/-- Absorption of the actual profile Volterra inequality. All integral convergence
and weighted-supremum finiteness are derived from bounded measurability. -/
theorem weighted_volterra_absorption {f : ℝ → ℝ} {a b θ h A B M : ℝ}
    (ha : -1 < a) (ha0 : a ≤ 0) (hθ : 0 < θ) (hbθ : b + 1 / 2 = θ)
    (hh : 0 < h) (hh1 : h ≤ 1) (_hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hf : Measurable f) (hf0 : ∀ t ∈ Ioc 0 h, 0 ≤ f t)
    (hfb : ∀ t ∈ Ioc 0 h, f t ≤ M)
    (hsmall : B * powerConstant a * h ^ θ ≤ 1 / 2)
    (hvolterra : ∀ t ∈ Ioc 0 h,
      f t ≤ A * t ^ a + B * t ^ b * (∫ u in (0 : ℝ)..t,
        (t - u) ^ (-(1 / 2 : ℝ)) * f u)) :
    ∀ t ∈ Ioc 0 h, f t ≤ 2 * A * t ^ a := by
  have hbounded := weightedValues_bddAbove ha0 hh1 hM hf0 hfb
  let S := weightedSup f a h
  have hS : 0 ≤ S := weightedSup_nonneg hh hbounded hf0
  have hK : 0 ≤ powerConstant a := (powerConstant_pos ha).le
  have hweight : ∀ t ∈ Ioc 0 h, t ^ (-a) * f t ≤ A + (B * powerConstant a * h ^ θ) * S := by
    intro t ht
    have hconv := singular_convolution_bound ha ht.1 hS hf
      (fun u hu => hf0 u ⟨hu.1, hu.2.le.trans ht.2⟩)
      (fun u hu => le_weightedSup_mul hbounded ⟨hu.1, hu.2.le.trans ht.2⟩)
    have he := mul_le_mul_of_nonneg_left (hvolterra t ht) (Real.rpow_nonneg ht.1.le (-a))
    have hc := mul_le_mul_of_nonneg_left hconv.2
      (mul_nonneg hB (Real.rpow_nonneg ht.1.le b))
    have hw := mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg ht.1.le (-a))
    have hp : t ^ (-a) * (A * t ^ a) = A := by
      rw [mul_left_comm, ← Real.rpow_add ht.1, neg_add_cancel, Real.rpow_zero, mul_one]
    have hk : t ^ (-a) * (B * t ^ b * (S * powerConstant a * t ^ (a + 1 / 2))) =
        B * powerConstant a * t ^ θ * S := by
      calc
        _ = B * powerConstant a * S * (t ^ (-a) * t ^ b * t ^ (a + 1 / 2)) := by ring
        _ = _ := by
          rw [← Real.rpow_add ht.1, ← Real.rpow_add ht.1,
            show -a + b + (a + 1 / 2) = θ by linarith]
          ring
    have htθ : t ^ θ ≤ h ^ θ := Real.rpow_le_rpow ht.1.le ht.2 hθ.le
    calc
      _ ≤ A + t ^ (-a) * (B * t ^ b * (S * powerConstant a * t ^ (a + 1 / 2))) := by
        rw [mul_add, hp] at he
        linarith
      _ = A + (B * powerConstant a * t ^ θ) * S := by rw [hk]
      _ ≤ _ := by gcongr
  have hsup : S ≤ A + (B * powerConstant a * h ^ θ) * S := by
    apply csSup_le (weightedValues_nonempty hh)
    rintro _ ⟨t, ht, rfl⟩
    exact hweight t ht
  have hSbound : S ≤ 2 * A := by nlinarith [mul_le_mul_of_nonneg_right hsmall hS]
  intro t ht
  exact (le_weightedSup_mul hbounded ht).trans
    (mul_le_mul_of_nonneg_right hSbound (Real.rpow_nonneg ht.1.le a))

/-- The exact exponents of the profile stability and variance displays. -/
theorem profile_volterra_stability {f : ℝ → ℝ} {β h A B M : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M) (hf : Measurable f)
    (hf0 : ∀ t ∈ Ioc 0 h, 0 ≤ f t) (hfb : ∀ t ∈ Ioc 0 h, f t ≤ M)
    (hsmall : B * powerConstant ((β - 1) / 4) * h ^ (β / 4) ≤ 1 / 2)
    (hvolterra : ∀ t ∈ Ioc 0 h,
      f t ≤ A * t ^ ((β - 1) / 4) + B * t ^ ((β - 2) / 4) *
        (∫ u in (0 : ℝ)..t, (t - u) ^ (-(1 / 2 : ℝ)) * f u)) :
    ∀ t ∈ Ioc 0 h,
      f t ≤ 2 * A * t ^ ((β - 1) / 4) ∧
      IntervalIntegrable (fun u => (t - u) ^ (-(1 / 2 : ℝ)) * f u) volume 0 t ∧
      (∫ u in (0 : ℝ)..t, (t - u) ^ (-(1 / 2 : ℝ)) * f u) ≤
        2 * A * powerConstant ((β - 1) / 4) * t ^ ((β + 1) / 4) := by
  have hstable := weighted_volterra_absorption (a := (β - 1) / 4) (b := (β - 2) / 4)
    (θ := β / 4) (by linarith) (by linarith) (by positivity) (by ring)
    hh hh1 hA hB hM hf hf0 hfb hsmall hvolterra
  intro t ht
  refine ⟨hstable t ht, ?_⟩
  have hc := singular_convolution_bound (a := (β - 1) / 4) (by linarith) ht.1
    (show 0 ≤ 2 * A by positivity) hf
    (fun u hu => hf0 u ⟨hu.1, hu.2.le.trans ht.2⟩)
    (fun u hu => hstable u ⟨hu.1, hu.2.le.trans ht.2⟩)
  simpa only [show (β - 1) / 4 + 1 / 2 = (β + 1) / 4 by ring] using hc

/-- The Hölder-input version contracts in the ordinary time supremum. -/
theorem profile_holder_volterra_stability {f : ℝ → ℝ} {β h A B M : ℝ}
    (hβ : 0 < β) (hh : 0 < h) (hh1 : h ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M) (hf : Measurable f)
    (hf0 : ∀ t ∈ Ioc 0 h, 0 ≤ f t) (hfb : ∀ t ∈ Ioc 0 h, f t ≤ M)
    (hsmall : 6 * B * h ^ (β / 4) ≤ 1 / 2)
    (hvolterra : ∀ t ∈ Ioc 0 h,
      f t ≤ A + B * t ^ ((β - 2) / 4) *
        (∫ u in (0 : ℝ)..t, (t - u) ^ (-(1 / 2 : ℝ)) * f u)) :
    ∀ t ∈ Ioc 0 h, f t ≤ 2 * A := by
  have hs : B * powerConstant 0 * h ^ (β / 4) ≤ 1 / 2 := by
    norm_num [powerConstant] at *
    nlinarith
  have hv : ∀ t ∈ Ioc 0 h,
      f t ≤ A * t ^ (0 : ℝ) + B * t ^ ((β - 2) / 4) *
        (∫ u in (0 : ℝ)..t, (t - u) ^ (-(1 / 2 : ℝ)) * f u) := by
    simpa only [Real.rpow_zero, mul_one] using hvolterra
  have he := weighted_volterra_absorption (a := 0) (b := (β - 2) / 4) (θ := β / 4)
    (by norm_num) le_rfl (by positivity) (by ring) hh hh1 hA hB hM hf hf0 hfb hs hv
  simpa only [Real.rpow_zero, mul_one] using he

/-- An explicit positive horizon satisfying the actual Volterra contraction constant. -/
theorem exists_absorption_horizon {a B θ : ℝ} (ha : -1 < a) (hB : 0 ≤ B) (hθ : 0 < θ) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧ B * powerConstant a * h ^ θ ≤ 1 / 2 := by
  let base : ℝ := 1 / (2 * (B * powerConstant a + 1))
  have hK : 0 ≤ powerConstant a := (powerConstant_pos ha).le
  have hprod : 0 ≤ B * powerConstant a := mul_nonneg hB hK
  have hbase : 0 < base := by dsimp [base]; positivity
  have hbase1 : base ≤ 1 := by
    dsimp [base]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (B * powerConstant a + 1))).mpr
    nlinarith
  let h := base ^ (1 / θ)
  have hh : 0 < h := Real.rpow_pos_of_pos hbase _
  have hh1 : h ≤ 1 := Real.rpow_le_one hbase.le hbase1 (by positivity)
  have hpow : h ^ θ = base := by
    dsimp [h]
    rw [← Real.rpow_mul hbase.le, one_div_mul_cancel hθ.ne', Real.rpow_one]
  refine ⟨h, hh, hh1, ?_⟩
  rw [hpow]
  dsimp [base]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0 < 2 * (B * powerConstant a + 1))).mpr
  nlinarith

/-- The second compatible-reference convolution, with the exact `β/2` gain. -/
theorem squared_profile_convolution_bound {f : ℝ → ℝ} {β h P D : ℝ}
    (hβ : -1 < β) (hh : 0 < h) (hP : 0 ≤ P) (hD : 0 ≤ D) (hf : Measurable f)
    (hf0 : ∀ t ∈ Ioo 0 h, 0 ≤ f t)
    (hfb : ∀ t ∈ Ioo 0 h, f t ≤ P * D * t ^ ((β - 1) / 4)) :
    IntervalIntegrable (fun t => (h - t) ^ (-(1 / 2 : ℝ)) * f t ^ 2) volume 0 h ∧
    (∫ t in (0 : ℝ)..h, (h - t) ^ (-(1 / 2 : ℝ)) * f t ^ 2) ≤
      P ^ 2 * D ^ 2 * powerConstant ((β - 1) / 2) * h ^ (β / 2) := by
  have hb : ∀ t ∈ Ioo 0 h, f t ^ 2 ≤ (P ^ 2 * D ^ 2) * t ^ ((β - 1) / 2) := by
    intro t ht
    have hs := (sq_le_sq₀ (hf0 t ht) (mul_nonneg (mul_nonneg hP hD)
      (Real.rpow_nonneg ht.1.le _))).mpr (hfb t ht)
    rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast ht.1.le,
      show (β - 1) / 4 * (2 : ℕ) = (β - 1) / 2 by ring] at hs
    exact hs
  have hc := singular_convolution_bound (a := (β - 1) / 2) (by linarith) hh
    (show 0 ≤ P ^ 2 * D ^ 2 by positivity) (hf.pow_const (2 : ℕ)) (fun _ _ => sq_nonneg _) hb
  simpa only [show (β - 1) / 2 + 1 / 2 = β / 2 by ring] using hc

/-- Heat-row energy is integrated at the actual stochastic isometry density.
The stochastic isometry itself is an explicit input, not silently assumed. -/
theorem compatible_reference_noise_bound {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (μ : Measure Ω) {Z : Ω → E}
    (_hZ : MemLp Z 2 μ) {f rowEnergy : ℝ → ℝ} {β h P D C : ℝ}
    (hβ : -1 < β) (hh : 0 < h) (hP : 0 ≤ P) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hf : Measurable f) (hr : Measurable rowEnergy)
    (hf0 : ∀ t ∈ Ioo 0 h, 0 ≤ f t)
    (hfb : ∀ t ∈ Ioo 0 h, f t ≤ P * D * t ^ ((β - 1) / 4))
    (hr0 : ∀ t ∈ Ioo 0 h, 0 ≤ rowEnergy t)
    (hrow : ∀ t ∈ Ioo 0 h, rowEnergy t ≤ C * ((h - t) ^ (-(1 / 2 : ℝ)) * f t ^ 2))
    (hisometry : (∫ ω, ‖Z ω‖ ^ 2 ∂μ) = ∫ t in (0 : ℝ)..h, rowEnergy t) :
    IntervalIntegrable rowEnergy volume 0 h ∧
    (∫ ω, ‖Z ω‖ ^ 2 ∂μ) ≤
      C * P ^ 2 * powerConstant ((β - 1) / 2) * h ^ (β / 2) * D ^ 2 := by
  have hc := squared_profile_convolution_bound hβ hh hP hD hf hf0 hfb
  have hrint : IntervalIntegrable rowEnergy volume 0 h := by
    apply (hc.1.const_mul C).mono_fun'
    · exact hr.aestronglyMeasurable
    · rw [uIoc_of_le hh.le]
      filter_upwards [ae_restrict_mem measurableSet_Ioc,
        ae_restrict_of_ae (volume.ae_ne h)] with t ht hth
      have ht' : t ∈ Ioo 0 h := ⟨ht.1, lt_of_le_of_ne ht.2 hth⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (hr0 t ht')]
      exact hrow t ht'
  refine ⟨hrint, ?_⟩
  rw [hisometry]
  calc
    _ ≤ ∫ t in (0 : ℝ)..h, C * ((h - t) ^ (-(1 / 2 : ℝ)) * f t ^ 2) :=
      intervalIntegral.integral_mono_on_of_le_Ioo hh.le hrint (hc.1.const_mul C) hrow
    _ = C * (∫ t in (0 : ℝ)..h, (h - t) ^ (-(1 / 2 : ℝ)) * f t ^ 2) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ C * (P ^ 2 * D ^ 2 * powerConstant ((β - 1) / 2) * h ^ (β / 2)) :=
      mul_le_mul_of_nonneg_left hc.2 hC
    _ = _ := by ring

/-- A centered compatible noise difference is orthogonal to the deterministic heat mean. -/
theorem centered_reference_energy {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Z : Ω → E} (hZ : MemLp Z 2 μ)
    (hmean : (∫ ω, Z ω ∂μ) = 0) (m : E) :
    (∫ ω, ‖m + Z ω‖ ^ 2 ∂μ) = ‖m‖ ^ 2 + ∫ ω, ‖Z ω‖ ^ 2 ∂μ := by
  have hi : Integrable Z μ := hZ.integrable (by norm_num)
  have hsq := (memLp_two_iff_integrable_sq_norm hZ.aestronglyMeasurable).mp hZ
  have hi2 : Integrable (fun ω => 2 * inner ℝ m (Z ω)) μ := (hi.const_inner m).const_mul 2
  have hic : Integrable (fun ω => ‖m‖ ^ 2 + 2 * inner ℝ m (Z ω)) μ :=
    (integrable_const _).add hi2
  simp_rw [norm_add_sq_real]
  rw [integral_add hic hsq,
    integral_add (f := fun _ : Ω => ‖m‖ ^ 2) (g := fun ω => 2 * inner ℝ m (Z ω)) (integrable_const _) hi2,
    integral_const_mul, integral_inner hi, hmean, inner_zero_right, mul_zero, add_zero]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]

/-- The total compatible reference remains uniformly L² stable on `h≤1`, once
its centered stochastic isometry energy has been established. -/
theorem compatible_reference_total_bound {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Z : Ω → E} (hZ : MemLp Z 2 μ)
    (hmean : (∫ ω, Z ω ∂μ) = 0) (m : E) {β h D K : ℝ}
    (hβ : 0 ≤ β) (hh : 0 < h) (hh1 : h ≤ 1) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hm : ‖m‖ ≤ D) (hnoise : (∫ ω, ‖Z ω‖ ^ 2 ∂μ) ≤ K * h ^ (β / 2) * D ^ 2) :
    (∫ ω, ‖m + Z ω‖ ^ 2 ∂μ) ≤ (1 + K) * D ^ 2 := by
  rw [centered_reference_energy μ hZ hmean m]
  have hm' := (sq_le_sq₀ (norm_nonneg _) hD).mpr hm
  have hhβ : h ^ (β / 2) ≤ 1 := Real.rpow_le_one hh.le hh1 (by positivity)
  have hn := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhβ hK) (sq_nonneg D)
  nlinarith

/-- The complete analytic compatible-reference stability chain: actual bounded
profile Volterra inequality, actual heat-row energy density, and an explicit
stochastic isometry imply the centered and total L² estimates. -/
theorem profile_reference_stability {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Z : Ω → E} (hZ : MemLp Z 2 μ)
    (hmean : (∫ ω, Z ω ∂μ) = 0) (m : E) {f rowEnergy : ℝ → ℝ} {β h A B M D C : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hf : Measurable f) (hr : Measurable rowEnergy)
    (hf0 : ∀ t ∈ Ioc 0 h, 0 ≤ f t) (hfb : ∀ t ∈ Ioc 0 h, f t ≤ M)
    (hsmall : B * powerConstant ((β - 1) / 4) * h ^ (β / 4) ≤ 1 / 2)
    (hvolterra : ∀ t ∈ Ioc 0 h,
      f t ≤ (A * D) * t ^ ((β - 1) / 4) + B * t ^ ((β - 2) / 4) *
        (∫ u in (0 : ℝ)..t, (t - u) ^ (-(1 / 2 : ℝ)) * f u))
    (hr0 : ∀ t ∈ Ioo 0 h, 0 ≤ rowEnergy t)
    (hrow : ∀ t ∈ Ioo 0 h, rowEnergy t ≤ C * ((h - t) ^ (-(1 / 2 : ℝ)) * f t ^ 2))
    (hisometry : (∫ ω, ‖Z ω‖ ^ 2 ∂μ) = ∫ t in (0 : ℝ)..h, rowEnergy t)
    (hm : ‖m‖ ≤ D) :
    (∫ ω, ‖Z ω‖ ^ 2 ∂μ) ≤
      (4 * C * A ^ 2 * powerConstant ((β - 1) / 2)) * h ^ (β / 2) * D ^ 2 ∧
    (∫ ω, ‖m + Z ω‖ ^ 2 ∂μ) ≤
      (1 + 4 * C * A ^ 2 * powerConstant ((β - 1) / 2)) * D ^ 2 := by
  have hp := profile_volterra_stability hβ hβ1 hh hh1 (mul_nonneg hA hD)
    hB hM hf hf0 hfb hsmall hvolterra
  have hprofile : ∀ t ∈ Ioo 0 h, f t ≤ (2 * A) * D * t ^ ((β - 1) / 4) := by
    intro t ht
    have he := (hp t ⟨ht.1, ht.2.le⟩).1
    convert he using 1
    ring
  have hn := (compatible_reference_noise_bound μ hZ (by linarith : -1 < β) hh
    (show 0 ≤ 2 * A by positivity) hD hC hf hr
    (fun t ht => hf0 t ⟨ht.1, ht.2.le⟩) hprofile hr0 hrow hisometry).2
  have hn' : (∫ ω, ‖Z ω‖ ^ 2 ∂μ) ≤
      (4 * C * A ^ 2 * powerConstant ((β - 1) / 2)) * h ^ (β / 2) * D ^ 2 := by
    convert hn using 1
    ring
  refine ⟨hn', compatible_reference_total_bound μ hZ hmean m hβ.le hh hh1 hD ?_ hm hn'⟩
  exact mul_nonneg (mul_nonneg (by positivity) (sq_nonneg A))
    (powerConstant_pos (by linarith : -1 < (β - 1) / 2)).le

end SHE.ProfileVolterra
