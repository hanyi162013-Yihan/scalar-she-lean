module

public import SHE.HeatPeriodicBounds

/-! Positive Gaussian envelopes after genuine integer periodization. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.HeatPeriodicEnvelope
open MeasureTheory Set Real SHE.HeatOverlap SHE.HeatPeriodicBounds SHE.HeatPeriodization

theorem centered_integer_shift_square {x : ℝ} (hx : |x| ≤ 1 / 2) {n : ℤ} (hn : n ≠ 0) :
    x ^ 2 / 2 + (n : ℝ) ^ 2 / 8 ≤ (x + n) ^ 2 := by
  have hn1 := integer_abs_one_le hn
  have hr : |(n : ℝ)| ≤ |x + n| + |x| := by
    have hh := abs_sub (x + n) x
    simpa only [add_sub_cancel_left] using hh
  have hnx : |x| ≤ |x + n| := by linarith
  have hn2 : |(n : ℝ)| / 2 ≤ |x + n| := by linarith
  have hs1 := (sq_le_sq₀ (abs_nonneg x) (abs_nonneg (x + n))).mpr hnx
  have hs2 := (sq_le_sq₀ (by positivity : 0 ≤ |(n : ℝ)| / 2) (abs_nonneg (x + n))).mpr hn2
  simp only [sq_abs, div_pow] at hs1 hs2
  nlinarith

theorem centered_gaussian_tail_envelope {t x : ℝ} (ht : 0 < t) (hx : |x| ≤ 1 / 2)
    {n : ℤ} (hn : n ≠ 0) :
    gaussianAmplitude t 0 (x + n) ≤
      ((sqrt (sqrt t))⁻¹ * exp (-x ^ 2 / (16 * t)) * (64 * t)) *
        (1 / (n : ℝ) ^ 2) := by
  have hnreal : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hs := centered_integer_shift_square hx hn
  have he : -(x + n) ^ 2 / (8 * t) ≤ -x ^ 2 / (16 * t) - (n : ℝ) ^ 2 / (64 * t) := by
    apply (div_le_iff₀ (by positivity : 0 < 8 * t)).mpr
    field_simp at *
    nlinarith
  have hnexp : exp (-(n : ℝ) ^ 2 / (64 * t)) ≤ 64 * t * (1 / (n : ℝ) ^ 2) := by
    have h := exp_neg_le_inverse (show 0 < (n : ℝ) ^ 2 / (64 * t) by positivity)
    convert! h using 1
    · congr 1
      ring
    · field_simp
  unfold gaussianAmplitude
  simp only [sub_zero]
  calc
    _ ≤ (sqrt (sqrt t))⁻¹ * exp (-x ^ 2 / (16 * t) - (n : ℝ) ^ 2 / (64 * t)) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr he) (by positivity)
    _ = (sqrt (sqrt t))⁻¹ * (exp (-x ^ 2 / (16 * t)) * exp (-(n : ℝ) ^ 2 / (64 * t))) := by
      simp only [sub_eq_add_neg, exp_add, neg_div]
    _ ≤ (sqrt (sqrt t))⁻¹ * (exp (-x ^ 2 / (16 * t)) * (64 * t * (1 / (n : ℝ) ^ 2))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnexp (exp_pos _).le) (by positivity)
    _ = _ := by ring

theorem centered_gaussian_periodization_envelope {t x : ℝ} (ht : 0 < t) (hx : |x| ≤ 1 / 2) :
    Summable (fun n : ℤ => gaussianAmplitude t 0 (x + n)) ∧
      (∑' n : ℤ, gaussianAmplitude t 0 (x + n)) ≤
        (sqrt (sqrt t))⁻¹ * (1 + 64 * t * inverseSquareSum) * exp (-x ^ 2 / (16 * t)) := by
  let k : ℝ := (sqrt (sqrt t))⁻¹ * exp (-x ^ 2 / (16 * t))
  let major : ℤ → ℝ := Function.update (fun n : ℤ => (k * (64 * t)) * (1 / (n : ℝ) ^ 2)) 0 k
  have hm : HasSum major (k * (1 + 64 * t * inverseSquareSum)) := by
    have hh := ((summable_inverseSquare.mul_left (k * (64 * t))).hasSum).update 0 k
    convert! hh using 1
    simp only [Int.cast_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, div_zero, mul_zero, sub_zero, tsum_mul_left]
    unfold inverseSquareSum
    ring
  have hb : ∀ n : ℤ, ‖gaussianAmplitude t 0 (x + n)‖ ≤ major n := by
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (gaussianAmplitude_nonneg _ _ _)]
    by_cases hn : n = 0
    · simp only [hn, major, Function.update_self, Int.cast_zero, add_zero,
        gaussianAmplitude, sub_zero, k]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply exp_le_exp.mpr
      apply (div_le_div_iff₀ (by positivity : 0 < 8 * t) (by positivity : 0 < 16 * t)).mpr
      nlinarith [sq_nonneg x]
    · rw [show major n = (k * (64 * t)) * (1 / (n : ℝ) ^ 2) by
        simp only [major, Function.update_of_ne hn]]
      exact centered_gaussian_tail_envelope ht hx hn
  refine ⟨hm.summable.of_norm_bounded hb, ?_⟩
  have hh := (le_abs_self (∑' n : ℤ, gaussianAmplitude t 0 (x + n))).trans
    (tsum_of_norm_bounded hm hb)
  convert! hh using 1
  dsimp only [k]
  ring

def centeredDifference (x a : ℝ) : ℝ := x - a - (⌊x - a + 1 / 2⌋ : ℤ)

theorem centeredDifference_bound (x a : ℝ) : |centeredDifference x a| ≤ 1 / 2 := by
  have hlo := Int.floor_le (x - a + 1 / 2)
  have hhi := Int.lt_floor_add_one (x - a + 1 / 2)
  unfold centeredDifference
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem centeredDifference_coe (x a : ℝ) :
    (centeredDifference x a : UnitAddCircle) = (x : UnitAddCircle) - (a : UnitAddCircle) := by
  simp only [centeredDifference, AddCircle.coe_sub]
  simp

theorem centeredDifference_abs (x a : ℝ) :
    |centeredDifference x a| = dist (x : UnitAddCircle) (a : UnitAddCircle) := by
  rw [dist_eq_norm, ← centeredDifference_coe]
  symm
  apply (AddCircle.norm_coe_eq_abs_iff 1 one_ne_zero).mpr
  simpa only [abs_one] using centeredDifference_bound x a

theorem gaussianAmplitude_centered_shift (t a x : ℝ) (n : ℤ) :
    gaussianAmplitude t a (x + n) = gaussianAmplitude t 0
      (centeredDifference x a + ((n + ⌊x - a + 1 / 2⌋ : ℤ) : ℝ)) := by
  unfold gaussianAmplitude
  have he : centeredDifference x a + ((n + ⌊x - a + 1 / 2⌋ : ℤ) : ℝ) - 0 = x + n - a := by
    simp only [centeredDifference, Int.cast_add]
    ring
  rw [he]

theorem gaussianAmplitude_reindex (t a x : ℝ) :
    (∑' n : ℤ, gaussianAmplitude t a (x + n)) =
      ∑' n : ℤ, gaussianAmplitude t 0 (centeredDifference x a + n) := by
  let k : ℤ := ⌊x - a + 1 / 2⌋
  have h := (Equiv.addRight k).tsum_eq
    (fun n : ℤ => gaussianAmplitude t 0 (centeredDifference x a + n))
  simpa only [Equiv.coe_addRight, k, ← gaussianAmplitude_centered_shift] using h

theorem summable_gaussianAmplitude_translates {t : ℝ} (ht : 0 < t) (a x : ℝ) :
    Summable (fun n : ℤ => gaussianAmplitude t a (x + n)) := by
  let k : ℤ := ⌊x - a + 1 / 2⌋
  have hc := (centered_gaussian_periodization_envelope ht (centeredDifference_bound x a)).1
  have hh := (Equiv.addRight k).summable_iff.mpr hc
  simpa only [Function.comp_def, Equiv.coe_addRight, k, ← gaussianAmplitude_centered_shift] using hh

theorem gaussianAmplitude_periodization_envelope {t : ℝ} (ht : 0 < t) (a x : ℝ) :
    (∑' n : ℤ, gaussianAmplitude t a (x + n)) ≤
      (sqrt (sqrt t))⁻¹ * (1 + 64 * t * inverseSquareSum) *
        exp (-(dist (x : UnitAddCircle) (a : UnitAddCircle)) ^ 2 / (16 * t)) := by
  rw [gaussianAmplitude_reindex]
  have h := (centered_gaussian_periodization_envelope ht (centeredDifference_bound x a)).2
  have hs : centeredDifference x a ^ 2 = (dist (x : UnitAddCircle) (a : UnitAddCircle)) ^ 2 := by
    rw [← centeredDifference_abs, sq_abs]
  simpa only [hs] using h

theorem norm_periodize_finite_heat_bound {q : ℕ} (t a : Fin q → ℝ) (f : ℝ → ℂ)
    {M : ℝ} (hM : 0 ≤ M) (ht : ∀ i, 0 < t i)
    (hb : ∀ y, ‖f y‖ ^ 2 ≤ M * ∑ i, (sqrt (t i))⁻¹ * exp (-(y - a i) ^ 2 / (4 * t i)))
    (x : ℝ) :
    ‖periodize f x‖ ≤ sqrt M * ∑ i, (sqrt (sqrt (t i)))⁻¹ *
      (1 + 64 * t i * inverseSquareSum) *
        exp (-(dist (x : UnitAddCircle) (a i : UnitAddCircle)) ^ 2 / (16 * t i)) := by
  have hs (i : Fin q) := summable_gaussianAmplitude_translates (ht i) (a i) x
  have hh : HasSum (fun n : ℤ => sqrt M * ∑ i, gaussianAmplitude (t i) (a i) (x + n))
      (sqrt M * ∑ i, ∑' n : ℤ, gaussianAmplitude (t i) (a i) (x + n)) := by
    exact (hasSum_sum (fun i (_ : i ∈ Finset.univ) => (hs i).hasSum)).mul_left (sqrt M)
  calc
    _ ≤ sqrt M * ∑ i, ∑' n : ℤ, gaussianAmplitude (t i) (a i) (x + n) :=
      tsum_of_norm_bounded hh (fun n => norm_bound_of_finite_heat_envelope t a f hM hb _)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun i _ => gaussianAmplitude_periodization_envelope (ht i) (a i) x))
      (sqrt_nonneg _)

def periodicEnvelopeConstant : ℝ := 1 + 64 * inverseSquareSum

theorem periodicEnvelopeConstant_pos : 0 < periodicEnvelopeConstant := by
  unfold periodicEnvelopeConstant
  linarith [inverseSquareSum_nonneg]

theorem finite_heat_periodization_pointwise_envelope {q : ℕ}
    (t a : Fin q → ℝ) (f : ℝ → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (ht : ∀ i, 0 < t i) (ht1 : ∀ i, t i ≤ 1)
    (hb : ∀ y, ‖f y‖ ^ 2 ≤ M * ∑ i, (sqrt (t i))⁻¹ * exp (-(y - a i) ^ 2 / (4 * t i)))
    (x : ℝ) :
    ‖periodize f x‖ ^ 2 ≤ M * periodicEnvelopeConstant ^ 2 * (q : ℝ) *
      ∑ i, (sqrt (t i))⁻¹ *
        exp (-(dist (x : UnitAddCircle) (a i : UnitAddCircle)) ^ 2 / (8 * t i)) := by
  let w : Fin q → ℝ := fun i => (sqrt (sqrt (t i)))⁻¹ *
    exp (-(dist (x : UnitAddCircle) (a i : UnitAddCircle)) ^ 2 / (16 * t i))
  have hw (i : Fin q) : 0 ≤ w i := by dsimp only [w]; positivity
  have hN : ‖periodize f x‖ ≤ sqrt M * periodicEnvelopeConstant * ∑ i, w i := by
    apply (norm_periodize_finite_heat_bound t a f hM ht hb x).trans
    calc
      _ ≤ sqrt M * ∑ i, periodicEnvelopeConstant * w i := by
        apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
        apply Finset.sum_le_sum
        intro i _
        have hc : 1 + 64 * t i * inverseSquareSum ≤ periodicEnvelopeConstant := by
          unfold periodicEnvelopeConstant
          have hh := mul_le_mul_of_nonneg_left (ht1 i) (show 0 ≤ 64 * inverseSquareSum by
            exact mul_nonneg (by norm_num) inverseSquareSum_nonneg)
          nlinarith
        have h := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ (sqrt (sqrt (t i)))⁻¹)
        have h' := mul_le_mul_of_nonneg_right h (exp_pos
          (-(dist (x : UnitAddCircle) (a i : UnitAddCircle)) ^ 2 / (16 * t i))).le
        convert! h' using 1
        dsimp only [w]
        ring
      _ = _ := by rw [← Finset.mul_sum]; ring
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin q => (1 : ℝ)) w
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hs
  have hw2 (i : Fin q) : w i ^ 2 = (sqrt (t i))⁻¹ *
      exp (-(dist (x : UnitAddCircle) (a i : UnitAddCircle)) ^ 2 / (8 * t i)) := by
    dsimp only [w]
    rw [mul_pow, inv_pow, sq_sqrt (sqrt_nonneg _), ← exp_nat_mul]
    congr 2
    norm_num
    ring
  have hn2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
    (mul_nonneg (sqrt_nonneg _) periodicEnvelopeConstant_pos.le)
    (Finset.sum_nonneg (fun i _ => hw i)))).mpr hN
  rw [mul_pow, mul_pow, sq_sqrt hM] at hn2
  calc
    _ ≤ M * periodicEnvelopeConstant ^ 2 * (∑ i, w i) ^ 2 := hn2
    _ ≤ M * periodicEnvelopeConstant ^ 2 * ((q : ℝ) * ∑ i, w i ^ 2) :=
      mul_le_mul_of_nonneg_left hs (mul_nonneg hM (sq_nonneg _))
    _ = _ := by simp_rw [hw2]; ring

end SHE.HeatPeriodicEnvelope
