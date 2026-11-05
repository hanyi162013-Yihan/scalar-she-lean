module

public import SHE.HeatLine

/-! Actual Gaussian overlap integrals, used to separate finite heat clusters.
The bounds apply to arbitrary measurable signed or complex functions under
the already proved physical Gaussian envelope. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.HeatOverlap
open MeasureTheory Real

theorem integral_shifted_gaussian (a c : ℝ) :
    (∫ x : ℝ, exp (-a * (x - c) ^ 2)) = sqrt (π / a) := by
  have h := integral_add_right_eq_self (μ := volume) (fun x : ℝ => exp (-a * x ^ 2)) (-c)
  simpa only [← sub_eq_add_neg, integral_gaussian] using h

theorem integrable_shifted_gaussian {a : ℝ} (ha : 0 < a) (c : ℝ) :
    Integrable (fun x : ℝ => exp (-a * (x - c) ^ 2)) := by
  have h := HeatLine.integrable_affine_iff (fun x : ℝ => exp (-a * x ^ 2)) (-c)
    (show (1 : ℝ) ≠ 0 by norm_num)
  simpa only [one_mul, neg_add_eq_sub] using h.mpr (integrable_exp_neg_mul_sq ha)

theorem gaussian_complete_square {a b : ℝ} (hab : a + b ≠ 0) (c d x : ℝ) :
    -a * (x - c) ^ 2 - b * (x - d) ^ 2 =
      -(a + b) * (x - (a * c + b * d) / (a + b)) ^ 2 -
        (a * b / (a + b)) * (c - d) ^ 2 := by
  field_simp
  ring

theorem gaussian_product_identity {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (c d x : ℝ) :
    exp (-a * (x - c) ^ 2) * exp (-b * (x - d) ^ 2) =
      exp (-(a * b / (a + b)) * (c - d) ^ 2) *
        exp (-(a + b) * (x - (a * c + b * d) / (a + b)) ^ 2) := by
  rw [← exp_add, ← exp_add]
  congr 1
  have h := gaussian_complete_square (show a + b ≠ 0 by positivity) c d x
  linarith

theorem integrable_gaussian_product {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (c d : ℝ) :
    Integrable (fun x : ℝ => exp (-a * (x - c) ^ 2) * exp (-b * (x - d) ^ 2)) := by
  simp_rw [gaussian_product_identity ha hb]
  exact (integrable_shifted_gaussian (add_pos ha hb) _).const_mul _

theorem integral_gaussian_product {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (c d : ℝ) :
    (∫ x : ℝ, exp (-a * (x - c) ^ 2) * exp (-b * (x - d) ^ 2)) =
      sqrt (π / (a + b)) * exp (-(a * b / (a + b)) * (c - d) ^ 2) := by
  simp_rw [gaussian_product_identity ha hb]
  rw [integral_const_mul, integral_shifted_gaussian, mul_comm]

theorem gaussian_norm_integrable {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    {A a c : ℝ} (ha : 0 < a) (hbound : ∀ x, ‖f x‖ ≤ A * exp (-a * (x - c) ^ 2)) :
    Integrable f ∧ (∫ x : ℝ, ‖f x‖) ≤ A * sqrt (π / a) := by
  have hmajor := (integrable_shifted_gaussian ha c).const_mul A
  have hi : Integrable f := hmajor.mono' hf (ae_of_all _ hbound)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x : ℝ, A * exp (-a * (x - c) ^ 2) := integral_mono hi.norm hmajor hbound
    _ = _ := by rw [integral_const_mul, integral_shifted_gaussian]

/-- Genuine bilinear overlap of arbitrary two functions with Gaussian
envelopes. Neither positivity nor independence of the inputs is needed. -/
theorem gaussian_cross_integral_bound {f g : ℝ → ℂ}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume)
    {A B a b c d : ℝ} (hA : 0 ≤ A) (_hB : 0 ≤ B) (ha : 0 < a) (hb : 0 < b)
    (hfb : ∀ x, ‖f x‖ ≤ A * exp (-a * (x - c) ^ 2))
    (hgb : ∀ x, ‖g x‖ ≤ B * exp (-b * (x - d) ^ 2)) :
    Integrable (fun x => f x * star (g x)) ∧
      ‖∫ x : ℝ, f x * star (g x)‖ ≤ A * B * sqrt (π / (a + b)) *
        exp (-(a * b / (a + b)) * (c - d) ^ 2) := by
  let major : ℝ → ℝ := fun x => A * B *
    (exp (-a * (x - c) ^ 2) * exp (-b * (x - d) ^ 2))
  have him : Integrable major := (integrable_gaussian_product ha hb c d).const_mul (A * B)
  have hm : ∀ x, ‖f x * star (g x)‖ ≤ major x := by
    intro x
    rw [norm_mul, norm_star]
    calc
      _ ≤ (A * exp (-a * (x - c) ^ 2)) * (B * exp (-b * (x - d) ^ 2)) :=
        mul_le_mul (hfb x) (hgb x) (norm_nonneg _) (mul_nonneg hA (exp_pos _).le)
      _ = _ := by dsimp only [major]; ring
  have hi : Integrable (fun x => f x * star (g x)) :=
    him.mono' (hf.mul hg.star) (ae_of_all _ hm)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x : ℝ, major x := norm_integral_le_of_norm_le him (ae_of_all _ hm)
    _ = _ := by
      dsimp only [major]
      rw [integral_const_mul, integral_gaussian_product ha hb]
      ring

theorem norm_gaussian_bound_of_sq {f : ℝ → ℂ} {M : ℝ} (hM : 0 ≤ M) (u : ℝ → ℝ)
    (hbound : ∀ x, ‖f x‖ ^ 2 ≤ M * exp (2 * u x)) :
    ∀ x, ‖f x‖ ≤ sqrt M * exp (u x) := by
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    _ ≤ M * exp (2 * u x) := hbound x
    _ = _ := by rw [mul_pow, sq_sqrt hM, ← exp_nat_mul]; norm_num

theorem heat_envelope_norm_bound {f : ℝ → ℂ} {C E T c : ℝ}
    (hC : 0 ≤ C) (hE : 0 ≤ E) (hT : 0 < T)
    (hbound : ∀ x, ‖f x‖ ^ 2 ≤ C * (sqrt T)⁻¹ * E * exp (-(x - c) ^ 2 / (4 * T))) :
    ∀ x, ‖f x‖ ≤ sqrt (C * (sqrt T)⁻¹ * E) * exp (-(x - c) ^ 2 / (8 * T)) := by
  apply norm_gaussian_bound_of_sq (by positivity)
    (fun x => -(x - c) ^ 2 / (8 * T))
  intro x
  have he : 2 * (-(x - c) ^ 2 / (8 * T)) = -(x - c) ^ 2 / (4 * T) := by ring
  simpa only [he] using hbound x

/-- Exact overlap bound associated to two physical heat envelopes. The
exponential records spatial separation and the square-root prefactor records
age separation. Both effects follow from the genuine line integral. -/
theorem heat_envelope_cross_bound {f g : ℝ → ℂ}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume)
    {C D E F T U c d : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hT : 0 < T) (hU : 0 < U)
    (hfb : ∀ x, ‖f x‖ ^ 2 ≤ C * (sqrt T)⁻¹ * E * exp (-(x - c) ^ 2 / (4 * T)))
    (hgb : ∀ x, ‖g x‖ ^ 2 ≤ D * (sqrt U)⁻¹ * F * exp (-(x - d) ^ 2 / (4 * U))) :
    Integrable (fun x => f x * star (g x)) ∧
      ‖∫ x : ℝ, f x * star (g x)‖ ≤
        sqrt (C * (sqrt T)⁻¹ * E) * sqrt (D * (sqrt U)⁻¹ * F) *
          sqrt (8 * π * (T * U) / (T + U)) * exp (-(c - d) ^ 2 / (8 * (T + U))) := by
  have hfb' := heat_envelope_norm_bound hC hE hT hfb
  have hgb' := heat_envelope_norm_bound hD hF hU hgb
  have h := gaussian_cross_integral_bound hf hg (sqrt_nonneg _) (sqrt_nonneg _)
    (a := 1 / (8 * T)) (b := 1 / (8 * U)) (c := c) (d := d)
    (by positivity) (by positivity)
    (by
      intro x
      have he : -(1 / (8 * T)) * (x - c) ^ 2 = -(x - c) ^ 2 / (8 * T) := by ring
      simpa only [he] using hfb' x)
    (by
      intro x
      have he : -(1 / (8 * U)) * (x - d) ^ 2 = -(x - d) ^ 2 / (8 * U) := by ring
      simpa only [he] using hgb' x)
  refine ⟨h.1, ?_⟩
  have he : π / (1 / (8 * T) + 1 / (8 * U)) = 8 * π * (T * U) / (T + U) := by
    field_simp
    ring
  have hx : -(1 / (8 * T) * (1 / (8 * U)) / (1 / (8 * T) + 1 / (8 * U))) * (c - d) ^ 2 =
      -(c - d) ^ 2 / (8 * (T + U)) := by
    field_simp
    ring
  simpa only [he, hx] using h.2

theorem heat_overlap_amplitude_identity {C D E F T U : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) (hF : 0 ≤ F) (hT : 0 < T) (hU : 0 < U) :
    sqrt (C * (sqrt T)⁻¹ * E) * sqrt (D * (sqrt U)⁻¹ * F) *
      sqrt (8 * π * (T * U) / (T + U)) =
      sqrt (8 * π * C * D) * sqrt E * sqrt F *
        sqrt (sqrt T * sqrt U / (T + U)) := by
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  simp only [mul_pow,
    sq_sqrt (show 0 ≤ C * (sqrt T)⁻¹ * E by positivity),
    sq_sqrt (show 0 ≤ D * (sqrt U)⁻¹ * F by positivity),
    sq_sqrt (show 0 ≤ 8 * π * (T * U) / (T + U) by positivity),
    sq_sqrt (show 0 ≤ 8 * π * C * D by positivity), sq_sqrt hE, sq_sqrt hF,
    sq_sqrt (show 0 ≤ sqrt T * sqrt U / (T + U) by positivity)]
  calc
    _ = (8 * π * C * D * E * F / (T + U)) * (T / sqrt T) * (U / sqrt U) := by ring
    _ = _ := by rw [div_sqrt, div_sqrt]; ring

def overlapWeight (T U c d : ℝ) : ℝ :=
  sqrt (sqrt T * sqrt U / (T + U)) * exp (-(c - d) ^ 2 / (8 * (T + U)))

theorem heat_envelope_cross_bound_normalized {f g : ℝ → ℂ}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume)
    {C D E F T U c d : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hT : 0 < T) (hU : 0 < U)
    (hfb : ∀ x, ‖f x‖ ^ 2 ≤ C * (sqrt T)⁻¹ * E * exp (-(x - c) ^ 2 / (4 * T)))
    (hgb : ∀ x, ‖g x‖ ^ 2 ≤ D * (sqrt U)⁻¹ * F * exp (-(x - d) ^ 2 / (4 * U))) :
    Integrable (fun x => f x * star (g x)) ∧
      ‖∫ x : ℝ, f x * star (g x)‖ ≤
        sqrt (8 * π * C * D) * sqrt E * sqrt F * overlapWeight T U c d := by
  obtain ⟨hi, hb⟩ := heat_envelope_cross_bound hf hg hC hD hE hF hT hU hfb hgb
  rw [heat_overlap_amplitude_identity hC hD hE hF hT hU] at hb
  exact ⟨hi, by simpa only [overlapWeight, mul_assoc] using hb⟩

theorem overlapWeight_nonneg (T U c d : ℝ) : 0 ≤ overlapWeight T U c d := by
  unfold overlapWeight
  positivity

theorem overlapWeight_symm (T U c d : ℝ) :
    overlapWeight T U c d = overlapWeight U T d c := by
  unfold overlapWeight
  rw [mul_comm (sqrt T), add_comm T, sub_sq_comm c]

theorem overlap_prefactor_le_one {T U : ℝ} (hT : 0 < T) (hU : 0 < U) :
    sqrt (sqrt T * sqrt U / (T + U)) ≤ 1 := by
  apply sqrt_le_one.mpr
  apply (div_le_one (add_pos hT hU)).mpr
  nlinarith [sq_sqrt hT.le, sq_sqrt hU.le, sq_nonneg (sqrt T - sqrt U)]

theorem overlapWeight_le_age_ratio {T U c d : ℝ} (hT : 0 < T) (hU : 0 < U) :
    overlapWeight T U c d ≤ sqrt (sqrt T / sqrt U) := by
  unfold overlapWeight
  have he : exp (-(c - d) ^ 2 / (8 * (T + U))) ≤ 1 := by
    apply exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  calc
    _ ≤ sqrt (sqrt T * sqrt U / (T + U)) :=
      mul_le_of_le_one_right (sqrt_nonneg _) he
    _ ≤ sqrt (sqrt T / sqrt U) := by
      apply sqrt_le_sqrt
      calc
        _ ≤ sqrt T * sqrt U / U :=
          div_le_div_of_nonneg_left (by positivity) hU (le_add_of_nonneg_left hT.le)
        _ = _ := by rw [mul_div_assoc, sqrt_div_self]; ring

theorem overlapWeight_le_age_small {T U c d ε : ℝ} (hT : 0 < T) (hU : 0 < U)
    (hε : 0 ≤ ε) (hsmall : T ≤ ε ^ 4 * U) : overlapWeight T U c d ≤ ε := by
  apply (overlapWeight_le_age_ratio hT hU).trans
  apply (sqrt_le_iff).mpr
  refine ⟨hε, ?_⟩
  apply (div_le_iff₀ (sqrt_pos.mpr hU)).mpr
  apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp
  rw [sq_sqrt hT.le, mul_pow, sq_sqrt hU.le]
  nlinarith

theorem overlapWeight_le_center {T U c d L : ℝ} (hT : 0 < T) (hU : 0 < U)
    (hL : 0 ≤ L) (hsep : L * sqrt (max T U) ≤ |c - d|) :
    overlapWeight T U c d ≤ exp (-(L ^ 2) / 16) := by
  have hM : 0 < max T U := lt_max_of_lt_left hT
  have hs := (sq_le_sq₀ (by positivity : 0 ≤ L * sqrt (max T U)) (abs_nonneg (c - d))).mpr hsep
  rw [mul_pow, sq_sqrt hM.le, sq_abs] at hs
  have hTU : T + U ≤ 2 * max T U := by linarith [le_max_left T U, le_max_right T U]
  have hq : L ^ 2 / 16 ≤ (c - d) ^ 2 / (8 * (T + U)) := by
    apply (div_le_div_iff₀ (by norm_num) (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hTU (sq_nonneg L)]
  unfold overlapWeight
  calc
    _ ≤ exp (-(c - d) ^ 2 / (8 * (T + U))) :=
      mul_le_of_le_one_left (exp_pos _).le (overlap_prefactor_le_one hT hU)
    _ ≤ _ := exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hq)

theorem exp_neg_le_inverse {x : ℝ} (hx : 0 < x) : exp (-x) ≤ 1 / x := by
  have h : x ≤ exp x := (by linarith : x ≤ x + 1).trans (add_one_le_exp x)
  have hi := one_div_le_one_div_of_le hx h
  simpa only [one_div, exp_neg] using hi

theorem overlapWeight_le_center_small {T U c d L ε : ℝ}
    (hT : 0 < T) (hU : 0 < U) (hε : 0 < ε) (hL : 1 ≤ L)
    (hlarge : 16 / ε ≤ L) (hsep : L * sqrt (max T U) ≤ |c - d|) :
    overlapWeight T U c d ≤ ε := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hpow : L ≤ L ^ 2 := by nlinarith
  have hεL : 16 ≤ ε * L := by simpa only [mul_comm] using (div_le_iff₀ hε).mp hlarge
  calc
    _ ≤ exp (-(L ^ 2) / 16) := overlapWeight_le_center hT hU hLpos.le hsep
    _ ≤ 1 / (L ^ 2 / 16) := by
      simpa only [neg_div] using exp_neg_le_inverse (show 0 < L ^ 2 / 16 by positivity)
    _ ≤ ε := by
      apply (div_le_iff₀ (by positivity : 0 < L ^ 2 / 16)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hpow hε.le]

/-- A single explicit large threshold makes every pair of separated scales
or separated centers almost orthogonal. -/
theorem exists_overlap_separation_threshold {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (T U c d : ℝ), 0 < T → 0 < U →
      (T > L * U ∨ U > L * T ∨ |c - d| > L * sqrt (max T U)) →
      overlapWeight T U c d ≤ ε := by
  let L : ℝ := max 1 (max (1 / ε ^ 4) (16 / ε))
  have hL : 1 ≤ L := le_max_left _ _
  have hLa : 1 / ε ^ 4 ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hLc : 16 / ε ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  have ha : 1 ≤ L * ε ^ 4 := (div_le_iff₀ (pow_pos hε 4)).mp hLa
  refine ⟨L, hL, ?_⟩
  intro T U c d hT hU hsep
  rcases hsep with hsep | hsep | hsep
  · rw [overlapWeight_symm]
    apply overlapWeight_le_age_small hU hT hε.le
    have h := mul_le_mul_of_nonneg_left hsep.le (pow_nonneg hε.le 4)
    nlinarith [mul_le_mul_of_nonneg_right ha hU.le]
  · apply overlapWeight_le_age_small hT hU hε.le
    have h := mul_le_mul_of_nonneg_left hsep.le (pow_nonneg hε.le 4)
    nlinarith [mul_le_mul_of_nonneg_right ha hT.le]
  · exact overlapWeight_le_center_small hT hU hε hL hLc hsep.le

end SHE.HeatOverlap
