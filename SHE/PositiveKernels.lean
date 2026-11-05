module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE
open MeasureTheory

/-! Positive averaging and high-moment truncation for the native kernel.
These statements use genuine integrals of random kernels. They do not
require independence between the random kernel and the actual input. -/

/-- A positive probability averaging preserves every even moment. -/
theorem even_moment_average_le {Y : Type*} [MeasurableSpace Y]
    (κ : Measure Y) [IsProbabilityMeasure κ] (m : ℕ) {f : Y → ℝ}
    (hf : Integrable f κ) (hfm : Integrable (fun y => f y ^ (2 * m)) κ) :
    (∫ y, f y ∂κ) ^ (2 * m) ≤ ∫ y, f y ^ (2 * m) ∂κ := by
  exact (even_two_mul m).convexOn_pow.map_integral_le
    (continuous_pow (2 * m)).continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hf hfm

/-- Heat-tree averaging preserves a uniform pointwise moment bound.
Fubini is performed on the actual product measure. No spatial supremum
moment and no independence of random amplitudes are used. -/
theorem averaged_random_kernel_moment_le
    {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (μ : Measure Ω) (κ : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure κ]
    (m : ℕ) (A : Ω × Y → ℝ) (C : ℝ)
    (hA : Integrable A (μ.prod κ))
    (hAm : Integrable (fun z => A z ^ (2 * m)) (μ.prod κ))
    (hC : ∀ᵐ y ∂κ, (∫ ω, A (ω,y) ^ (2 * m) ∂μ) ≤ C) :
    (∫ ω, (∫ y, A (ω,y) ∂κ) ^ (2 * m) ∂μ) ≤ C := by
  have havg : Integrable (fun ω => (∫ y, A (ω,y) ∂κ) ^ (2 * m)) μ := by
    apply hAm.integral_prod_left.mono'
      (hA.integral_prod_left.aestronglyMeasurable.pow (2 * m))
    filter_upwards [hA.prod_right_ae, hAm.prod_right_ae] with ω hω hωm
    rw [Real.norm_eq_abs, abs_of_nonneg ((even_two_mul m).pow_nonneg _)]
    exact even_moment_average_le κ m hω hωm
  calc
    _ ≤ ∫ ω, ∫ y, A (ω,y) ^ (2 * m) ∂κ ∂μ := by
      apply integral_mono_ae havg hAm.integral_prod_left
      filter_upwards [hA.prod_right_ae, hAm.prod_right_ae] with ω hω hωm
      exact even_moment_average_le κ m hω hωm
    _ = ∫ y, ∫ ω, A (ω,y) ^ (2 * m) ∂μ ∂κ := integral_integral_swap hAm
    _ ≤ ∫ _ : Y, C ∂κ := integral_mono_ae hAm.integral_prod_right (integrable_const C) hC
    _ = C := by simp

/-- The bad amplitude is cut before the true right factor of a kernel. -/
def badAmplitude (R a : ℝ) := if R < |a| then a else 0

theorem badAmplitude_measurable {Ω : Type*} [MeasurableSpace Ω]
    {A : Ω → ℝ} (hA : Measurable A) (R : ℝ) :
    Measurable (fun ω => badAmplitude R (A ω)) := by
  exact hA.ite (measurableSet_lt measurable_const (continuous_abs.measurable.comp hA)) measurable_const

/-- A pointwise high-moment tail bound; the exponent may be chosen
arbitrarily large at any fixed word order. -/
theorem badAmplitude_sq_le {R a : ℝ} (hR : 0 < R) (m : ℕ) :
    badAmplitude R a ^ 2 ≤ |a| ^ (2 * m + 2) / R ^ (2 * m) := by
  unfold badAmplitude
  split_ifs with ha
  · apply (le_div_iff₀ (pow_pos hR _)).mpr
    rw [pow_add, sq_abs]
    have hp : R ^ (2 * m) ≤ |a| ^ (2 * m) :=
      pow_le_pow_left₀ hR.le ha.le _
    nlinarith [mul_le_mul_of_nonneg_right hp (sq_nonneg a)]
  · simp only [zero_pow (by decide : 2 ≠ 0)]
    positivity

/-- The bad kernel tail follows from a genuine high moment of its
normalized amplitude, with no assertion about an adapted multiplier. -/
theorem integral_badAmplitude_sq_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {A : Ω → ℝ} {R C : ℝ} (hR : 0 < R) (m : ℕ)
    (hbad : Integrable (fun ω => badAmplitude R (A ω) ^ 2) μ)
    (hmoment : Integrable (fun ω => |A ω| ^ (2 * m + 2)) μ)
    (hC : (∫ ω, |A ω| ^ (2 * m + 2) ∂μ) ≤ C) :
    (∫ ω, badAmplitude R (A ω) ^ 2 ∂μ) ≤ C / R ^ (2 * m) := by
  calc
    _ ≤ ∫ ω, |A ω| ^ (2 * m + 2) / R ^ (2 * m) ∂μ :=
      integral_mono hbad (hmoment.div_const _) fun _ => badAmplitude_sq_le hR m
    _ = (∫ ω, |A ω| ^ (2 * m + 2) ∂μ) / R ^ (2 * m) := integral_div _ _
    _ ≤ _ := div_le_div_of_nonneg_right hC (pow_nonneg hR.le _)

/-- High-moment integrability itself guarantees the bad square is
integrable. The discarded kernel has a genuine finite second moment. -/
theorem badAmplitude_sq_integrable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {A : Ω → ℝ} {R : ℝ} (hR : 0 < R) (m : ℕ)
    (hA : Measurable A)
    (hmoment : Integrable (fun ω => |A ω| ^ (2 * m + 2)) μ) :
    Integrable (fun ω => badAmplitude R (A ω) ^ 2) μ := by
  apply (hmoment.div_const (R ^ (2 * m))).mono'
    ((badAmplitude_measurable hA R).pow_const 2).aestronglyMeasurable
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact badAmplitude_sq_le hR m

/-- At a cutoff `Λ^ε`, any prescribed polynomial tail is obtained by
choosing a sufficiently high fixed moment. -/
theorem badAmplitude_polynomial_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {A : Ω → ℝ} {Λ ε B C : ℝ} (hΛ : 1 ≤ Λ) (hC : 0 ≤ C)
    (m : ℕ) (hm : B ≤ ε * (2 * m))
    (hbad : Integrable (fun ω => badAmplitude (Λ ^ ε) (A ω) ^ 2) μ)
    (hmoment : Integrable (fun ω => |A ω| ^ (2 * m + 2)) μ)
    (hbound : (∫ ω, |A ω| ^ (2 * m + 2) ∂μ) ≤ C) :
    (∫ ω, badAmplitude (Λ ^ ε) (A ω) ^ 2 ∂μ) ≤ C * Λ ^ (-B) := by
  have hΛ0 : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hb := integral_badAmplitude_sq_le μ (Real.rpow_pos_of_pos hΛ0 ε) m hbad hmoment hbound
  calc
    _ ≤ C / (Λ ^ ε) ^ (2 * m) := hb
    _ = C * Λ ^ (-(ε * (2 * m))) := by
      rw [← Real.rpow_mul_natCast hΛ0.le, div_eq_mul_inv, ← Real.rpow_neg hΛ0.le]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hΛ (by linarith)) hC

theorem exists_tail_moment {ε B : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, B ≤ ε * (2 * m) := by
  obtain ⟨m,hm⟩ := exists_nat_ge (B / (2 * ε))
  refine ⟨m, ?_⟩
  have := (div_le_iff₀ (by positivity : 0 < 2 * ε)).mp hm
  nlinarith

section WeightedKernels
variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
variable (μ : Measure Ω) (ν : Measure Z) [IsProbabilityMeasure μ] [SFinite ν]

/-- Uniform pointwise moments plus a deterministic square-integrable
envelope imply genuine integrability on the product space. -/
theorem weighted_kernel_moment_integrable
    (A : Ω × Z → ℝ) (H : Z → ℝ) (n : ℕ) (C : ℝ) (_hC : 0 ≤ C)
    (hA : Measurable A) (hH : Measurable H) (hH2 : Integrable (fun z => H z ^ 2) ν)
    (hAn : ∀ᵐ z ∂ν, Integrable (fun ω => |A (ω,z)| ^ n) μ)
    (hbound : ∀ᵐ z ∂ν, (∫ ω, |A (ω,z)| ^ n ∂μ) ≤ C) :
    Integrable (fun p : Ω × Z => H p.2 ^ 2 * |A p| ^ n) (μ.prod ν) := by
  let G : Ω × Z → ℝ := fun p => H p.2 ^ 2 * |A p| ^ n
  have hG : Measurable G := ((hH.comp measurable_snd).pow_const 2).mul
    ((continuous_abs.measurable.comp hA).pow_const n)
  apply (integrable_prod_iff' hG.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [hAn] with z hz
    exact hz.const_mul (H z ^ 2)
  · apply (hH2.const_mul C).mono'
      hG.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
    filter_upwards [hbound] with z hz
    have he : (∫ ω, ‖G (ω,z)‖ ∂μ) = H z ^ 2 * ∫ ω, |A (ω,z)| ^ n ∂μ := by
      simp only [G, Real.norm_eq_abs, abs_mul, abs_pow, sq_abs, abs_abs]
      exact integral_const_mul _ _
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), he]
    simpa only [mul_comm C] using mul_le_mul_of_nonneg_left hz (sq_nonneg (H z))

theorem weighted_kernel_moment_bound
    (A : Ω × Z → ℝ) (H : Z → ℝ) (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hA : Measurable A) (hH : Measurable H) (hH2 : Integrable (fun z => H z ^ 2) ν)
    (hAn : ∀ᵐ z ∂ν, Integrable (fun ω => |A (ω,z)| ^ n) μ)
    (hbound : ∀ᵐ z ∂ν, (∫ ω, |A (ω,z)| ^ n ∂μ) ≤ C) :
    (∫ p : Ω × Z, H p.2 ^ 2 * |A p| ^ n ∂(μ.prod ν)) ≤ C * ∫ z, H z ^ 2 ∂ν := by
  have hG := weighted_kernel_moment_integrable μ ν A H n C hC hA hH hH2 hAn hbound
  rw [integral_prod_symm _ hG, ← integral_const_mul]
  apply integral_mono_ae hG.integral_prod_right (hH2.const_mul C)
  filter_upwards [hbound] with z hz
  rw [integral_const_mul]
  simpa only [mul_comm C] using mul_le_mul_of_nonneg_left hz (sq_nonneg (H z))

/-- The manuscript's bad-kernel estimate on its actual spatial product
space. Only pointwise moments of the normalized amplitude are needed;
there is no spatial supremum or independence hypothesis. -/
theorem weighted_bad_kernel_bound
    (A : Ω × Z → ℝ) (H : Z → ℝ) (m : ℕ) (C : ℝ) {R : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C)
    (hA : Measurable A) (hH : Measurable H) (hH2 : Integrable (fun z => H z ^ 2) ν)
    (hAn : ∀ᵐ z ∂ν, Integrable (fun ω => |A (ω,z)| ^ (2 * m + 2)) μ)
    (hbound : ∀ᵐ z ∂ν, (∫ ω, |A (ω,z)| ^ (2 * m + 2) ∂μ) ≤ C) :
    (∫ ω, ∫ z, (H z * badAmplitude R (A (ω,z))) ^ 2 ∂ν ∂μ) ≤
      C / R ^ (2 * m) * ∫ z, H z ^ 2 ∂ν := by
  let G : Ω × Z → ℝ := fun p => H p.2 ^ 2 * |A p| ^ (2 * m + 2)
  let B : Ω × Z → ℝ := fun p => (H p.2 * badAmplitude R (A p)) ^ 2
  have hG : Integrable G (μ.prod ν) :=
    weighted_kernel_moment_integrable μ ν A H (2 * m + 2) C hC hA hH hH2 hAn hbound
  have hBm : Measurable B := ((hH.comp measurable_snd).mul (badAmplitude_measurable hA R)).pow_const 2
  have hpoint : ∀ p, B p ≤ G p / R ^ (2 * m) := by
    intro p
    dsimp [B, G]
    rw [mul_pow, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (badAmplitude_sq_le hR m) (sq_nonneg _)
  have hB : Integrable B (μ.prod ν) := by
    apply (hG.div_const _).mono' hBm.aestronglyMeasurable
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint p
  calc
    _ = ∫ p, B p ∂(μ.prod ν) := (integral_prod B hB).symm
    _ ≤ ∫ p, G p / R ^ (2 * m) ∂(μ.prod ν) := integral_mono hB (hG.div_const _) hpoint
    _ = (∫ p, G p ∂(μ.prod ν)) / R ^ (2 * m) := integral_div _ _
    _ ≤ (C * ∫ z, H z ^ 2 ∂ν) / R ^ (2 * m) :=
      div_le_div_of_nonneg_right
        (weighted_kernel_moment_bound μ ν A H (2 * m + 2) C hC hA hH hH2 hAn hbound)
        (pow_nonneg hR.le _)
    _ = _ := by ring

end WeightedKernels

end SHE
