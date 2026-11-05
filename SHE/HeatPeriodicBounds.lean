module

public import SHE.HeatPeriodization

/-! Quantitative integer tails for actual Gaussian periodization. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.HeatPeriodicBounds
open MeasureTheory Set Real SHE.HeatOverlap SHE.HeatPeriodization

def inverseSquareSum : ℝ := ∑' n : ℤ, 1 / (n : ℝ) ^ 2

theorem summable_inverseSquare : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) :=
  Real.summable_one_div_int_pow.mpr (by norm_num)

theorem inverseSquareSum_nonneg : 0 ≤ inverseSquareSum :=
  tsum_nonneg (fun _ => by positivity)

theorem integer_abs_one_le {n : ℤ} (hn : n ≠ 0) : (1 : ℝ) ≤ |(n : ℝ)| := by
  have h : (1 : ℤ) ≤ |n| := by
    have hp := abs_pos.mpr hn
    omega
  exact_mod_cast h

theorem integer_shift_distance {x a η : ℝ} (_hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hx : |x| ≤ 1 / 2) (ha : |a| ≤ 1 / 2 - η) {n : ℤ} (hn : n ≠ 0) :
    η * |(n : ℝ)| ≤ |x + n - a| := by
  have hn1 := integer_abs_one_le hn
  have hxa : |x - a| ≤ 1 - η := (abs_sub _ _).trans (by linarith)
  have hr : |(n : ℝ)| ≤ |x + n - a| + |x - a| := by
    have h := abs_sub (x + n - a) (x - a)
    have he : (x + n - a) - (x - a) = (n : ℝ) := by ring
    simpa only [he] using h
  have hm := mul_nonneg (sub_nonneg.mpr hη1) (sub_nonneg.mpr hn1)
  nlinarith

theorem integer_gaussian_tail_bound {t η x a : ℝ} (ht : 0 < t) (hη : 0 < η)
    (hη1 : η ≤ 1) (hx : |x| ≤ 1 / 2) (ha : |a| ≤ 1 / 2 - η)
    {n : ℤ} (hn : n ≠ 0) :
    exp (-(x + n - a) ^ 2 / (8 * t)) ≤ (8 * t / η ^ 2) * (1 / (n : ℝ) ^ 2) := by
  have hnreal : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hd := integer_shift_distance hη.le hη1 hx ha hn
  have hdp : 0 < |x + n - a| := (mul_pos hη (abs_pos.mpr hnreal)).trans_le hd
  have hdz : x + n - a ≠ 0 := abs_pos.mp hdp
  have hd2 : η ^ 2 * (n : ℝ) ^ 2 ≤ (x + n - a) ^ 2 := by
    have hs := (sq_le_sq₀ (by positivity : 0 ≤ η * |(n : ℝ)|) (abs_nonneg _)).mpr hd
    simpa only [mul_pow, sq_abs] using hs
  calc
    _ ≤ 1 / ((x + n - a) ^ 2 / (8 * t)) := by
      simpa only [neg_div] using exp_neg_le_inverse
        (show 0 < (x + n - a) ^ 2 / (8 * t) by positivity)
    _ ≤ 1 / (η ^ 2 * (n : ℝ) ^ 2 / (8 * t)) :=
      one_div_le_one_div_of_le (by positivity)
        (div_le_div_of_nonneg_right hd2 (by positivity))
    _ = _ := by field_simp

def gaussianAmplitude (t a x : ℝ) : ℝ :=
  (sqrt (sqrt t))⁻¹ * exp (-(x - a) ^ 2 / (8 * t))

theorem gaussianAmplitude_nonneg (t a x : ℝ) : 0 ≤ gaussianAmplitude t a x := by
  unfold gaussianAmplitude
  positivity

theorem gaussianAmplitude_sq (t a x : ℝ) :
    gaussianAmplitude t a x ^ 2 = (sqrt t)⁻¹ * exp (-(x - a) ^ 2 / (4 * t)) := by
  unfold gaussianAmplitude
  rw [mul_pow, inv_pow, sq_sqrt (sqrt_nonneg _), ← exp_nat_mul]
  congr 2
  norm_num
  ring

theorem norm_bound_of_finite_heat_envelope {q : ℕ} (t a : Fin q → ℝ) (f : ℝ → ℂ)
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, ‖f x‖ ^ 2 ≤ M * ∑ i, (sqrt (t i))⁻¹ * exp (-(x - a i) ^ 2 / (4 * t i))) :
    ∀ x, ‖f x‖ ≤ sqrt M * ∑ i, gaussianAmplitude (t i) (a i) x := by
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sqrt_nonneg _)
    (Finset.sum_nonneg (fun _ _ => gaussianAmplitude_nonneg _ _ _)))).mp
  rw [mul_pow, sq_sqrt hM]
  calc
    _ ≤ M * ∑ i, gaussianAmplitude (t i) (a i) x ^ 2 := by
      simpa only [gaussianAmplitude_sq] using hb x
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => gaussianAmplitude_nonneg _ _ _)) hM

theorem gaussianAmplitude_integer_tail {t η x a : ℝ} (ht : 0 < t) (hη : 0 < η)
    (hη1 : η ≤ 1) (hx : |x| ≤ 1 / 2) (ha : |a| ≤ 1 / 2 - η)
    {n : ℤ} (hn : n ≠ 0) :
    gaussianAmplitude t a (x + n) ≤
      ((sqrt (sqrt t))⁻¹ * (8 * t / η ^ 2)) * (1 / (n : ℝ) ^ 2) := by
  unfold gaussianAmplitude
  exact (mul_le_mul_of_nonneg_left
    (integer_gaussian_tail_bound ht hη hη1 hx ha hn) (by positivity)).trans_eq (by ring)

theorem summable_integer_translate_of_tail {f : ℝ → ℂ} {x A : ℝ}
    (hbound : ∀ n : ℤ, n ≠ 0 → ‖f (x + n)‖ ≤ A * (1 / (n : ℝ) ^ 2)) :
    Summable (fun n : ℤ => f (x + n)) := by
  let major : ℤ → ℝ := Function.update (fun n : ℤ => A * (1 / (n : ℝ) ^ 2)) 0 ‖f x‖
  have hm : Summable major := (summable_inverseSquare.mul_left A).update 0 ‖f x‖
  apply hm.of_norm_bounded
  intro n
  by_cases hn : n = 0
  · simp only [hn, major, Function.update_self, Int.cast_zero, add_zero, le_refl]
  · simpa only [major, Function.update_of_ne hn] using hbound n hn

theorem norm_periodize_sub_of_tail {f : ℝ → ℂ} {x A : ℝ} (_hA : 0 ≤ A)
    (hbound : ∀ n : ℤ, n ≠ 0 → ‖f (x + n)‖ ≤ A * (1 / (n : ℝ) ^ 2)) :
    ‖periodize f x - f x‖ ≤ A * inverseSquareSum := by
  have hs := summable_integer_translate_of_tail hbound
  rw [periodize, hs.tsum_eq_add_tsum_ite 0]
  simp only [Int.cast_zero, add_zero, add_sub_cancel_left]
  unfold inverseSquareSum
  rw [← tsum_mul_left]
  apply tsum_of_norm_bounded ((summable_inverseSquare.mul_left A).hasSum)
  intro n
  by_cases hn : n = 0
  · simp only [hn, ite_true, norm_zero, Int.cast_zero, zero_pow, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, div_zero, mul_zero, le_refl]
  · simpa only [hn, ite_false] using hbound n hn

theorem norm_periodize_sub_finite_heat_envelope {q : ℕ} (t a : Fin q → ℝ) (f : ℝ → ℂ)
    {M η x : ℝ} (hM : 0 ≤ M) (ht : ∀ i, 0 < t i) (hη : 0 < η) (hη1 : η ≤ 1)
    (hx : |x| ≤ 1 / 2) (ha : ∀ i, |a i| ≤ 1 / 2 - η)
    (hb : ∀ y, ‖f y‖ ^ 2 ≤ M * ∑ i, (sqrt (t i))⁻¹ * exp (-(y - a i) ^ 2 / (4 * t i))) :
    ‖periodize f x - f x‖ ≤ sqrt M *
      (∑ i, (sqrt (sqrt (t i)))⁻¹ * (8 * t i / η ^ 2)) * inverseSquareSum := by
  apply norm_periodize_sub_of_tail (mul_nonneg (sqrt_nonneg M)
    (Finset.sum_nonneg (fun i _ => by have hti := ht i; positivity)))
  intro n hn
  calc
    _ ≤ sqrt M * ∑ i, gaussianAmplitude (t i) (a i) (x + n) :=
      norm_bound_of_finite_heat_envelope t a f hM hb _
    _ ≤ sqrt M * ∑ i, (((sqrt (sqrt (t i)))⁻¹ * (8 * t i / η ^ 2)) * (1 / (n : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ =>
        gaussianAmplitude_integer_tail (ht i) hη hη1 hx (ha i) hn)) (sqrt_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem heat_amplitude_scale_bound {t h : ℝ} (ht : 0 < t) (hth : t ≤ h) (hh : h ≤ 1) :
    (sqrt (sqrt t))⁻¹ * t ≤ sqrt h := by
  have hut : sqrt t ≤ 1 := sqrt_le_one.mpr (hth.trans hh)
  have hroot : sqrt t ≤ sqrt (sqrt t) :=
    le_sqrt_of_sq_le (by nlinarith [sqrt_nonneg t])
  calc
    _ = t / sqrt (sqrt t) := by ring
    _ ≤ sqrt t := by
      apply (div_le_iff₀ (sqrt_pos.mpr (sqrt_pos.mpr ht))).mpr
      nlinarith [sq_sqrt ht.le, mul_le_mul_of_nonneg_left hroot (sqrt_nonneg t)]
    _ ≤ sqrt h := sqrt_le_sqrt hth

theorem norm_periodize_sub_finite_heat_uniform {q : ℕ} (t a : Fin q → ℝ) (f : ℝ → ℂ)
    {M η x h : ℝ} (hM : 0 ≤ M) (ht : ∀ i, 0 < t i) (hth : ∀ i, t i ≤ h)
    (hh : h ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) (hx : |x| ≤ 1 / 2)
    (ha : ∀ i, |a i| ≤ 1 / 2 - η)
    (hb : ∀ y, ‖f y‖ ^ 2 ≤ M * ∑ i, (sqrt (t i))⁻¹ * exp (-(y - a i) ^ 2 / (4 * t i))) :
    ‖periodize f x - f x‖ ≤ sqrt M * ((q : ℝ) * (8 / η ^ 2) * sqrt h) * inverseSquareSum := by
  apply (norm_periodize_sub_finite_heat_envelope t a f hM ht hη hη1 hx ha hb).trans
  apply mul_le_mul_of_nonneg_right _ inverseSquareSum_nonneg
  apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg M)
  calc
    _ ≤ ∑ _ : Fin q, (8 / η ^ 2) * sqrt h := by
      apply Finset.sum_le_sum
      intro i _
      have hs := mul_le_mul_of_nonneg_left (heat_amplitude_scale_bound (ht i) (hth i) hh)
        (show 0 ≤ 8 / η ^ 2 by positivity)
      convert! hs using 1
      ring
    _ = _ := by simp; ring

end SHE.HeatPeriodicBounds
