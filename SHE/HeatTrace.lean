module

public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.HeatTrace
open MeasureTheory Set

/-- Two even sequences ordered in the same way have maximal correlation
at zero shift. This is the precise rearrangement used in the one-weight
heat trace; it involves a genuine infinite sum over Fourier frequencies. -/
theorem correlation_le_centered {f g : ℤ → ℝ}
    (hf : ∀ n, f (-n) = f n) (hg : ∀ n, g (-n) = g n)
    (horder : ∀ k l, 0 ≤ (f k - f l) * (g k - g l))
    (j : ℤ) (hdiag : Summable (fun k => f k * g k))
    (hcross : Summable (fun k => f k * g (k - j))) :
    (∑' k, f k * g (k - j)) ≤ ∑' k, f k * g k := by
  let e : ℤ ≃ ℤ :=
    { toFun := fun k => j - k
      invFun := fun k => j - k
      left_inv := by intro k; dsimp; ring
      right_inv := by intro k; dsimp; ring }
  let s : ℤ ≃ ℤ :=
    { toFun := fun k => k - j
      invFun := fun k => k + j
      left_inv := by intro k; dsimp; ring
      right_inv := by intro k; dsimp; ring }
  have heq : (fun k => f (e k) * g (e k - j)) = (fun k => f (k - j) * g k) := by
    funext k
    dsimp [e]
    rw [show j - k = -(k - j) by ring, hf, show -(k - j) - j = -k by ring, hg]
  have hcross' : Summable (fun k => f (k - j) * g k) := by
    rw [← heq]
    exact e.summable_iff.mpr hcross
  have hcross_eq : (∑' k, f (k - j) * g k) = ∑' k, f k * g (k - j) := by
    rw [← heq]
    exact e.tsum_eq (fun k : ℤ => f k * g (k-j))
  have hdiag' : Summable (fun k => f (k - j) * g (k - j)) := s.summable_iff.mpr hdiag
  have hdiag_eq : (∑' k, f (k - j) * g (k - j)) = ∑' k, f k * g k :=
    s.tsum_eq (fun k : ℤ => f k * g k)
  have hpoint : ∀ k, f k * g (k-j) + f (k-j) * g k ≤
      f k * g k + f (k-j) * g (k-j) := by
    intro k
    nlinarith [horder k (k-j)]
  have hsum := (hcross.add hcross').tsum_le_tsum hpoint (hdiag.add hdiag')
  rw [hcross.tsum_add hcross', hdiag.tsum_add hdiag', hcross_eq, hdiag_eq] at hsum
  linarith

/-- The massive heat multiplier on the Fourier lattice. -/
def multiplier (Λ ρ t x : ℝ) := (Λ + x ^ (2 : ℕ)) ^ (-ρ) * Real.exp (-t * x ^ (2 : ℕ))

theorem multiplier_nonneg {Λ ρ t x : ℝ} (hΛ : 0 ≤ Λ) : 0 ≤ multiplier Λ ρ t x := by
  unfold multiplier
  positivity

theorem multiplier_even (Λ ρ t x : ℝ) : multiplier Λ ρ t (-x) = multiplier Λ ρ t x := by
  simp [multiplier]

theorem multiplier_antitone {Λ ρ t : ℝ} (hΛ : 0 < Λ) (hρ : 0 ≤ ρ) (ht : 0 ≤ t) :
    AntitoneOn (multiplier Λ ρ t) (Ici 0) := by
  intro x hx y hy hxy
  have hs : x ^ (2 : ℕ) ≤ y ^ (2 : ℕ) := pow_le_pow_left₀ hx hxy 2
  apply mul_le_mul
  · exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  · exact Real.exp_le_exp.mpr (by nlinarith)
  · exact Real.exp_pos _ |>.le
  · exact Real.rpow_nonneg (by positivity) _

theorem multiplier_continuous {Λ ρ t : ℝ} (hΛ : 0 < Λ) :
    Continuous (multiplier Λ ρ t) := by
  unfold multiplier
  apply Continuous.mul
  · exact (continuous_const.add (continuous_pow 2)).rpow_const
      (fun x => Or.inl (ne_of_gt (by positivity : 0 < Λ + x ^ (2 : ℕ))))
  · fun_prop

theorem multiplier_integrable {Λ ρ t : ℝ} (hΛ : 0 < Λ) (hρ : 0 ≤ ρ) (ht : 0 < t) :
    Integrable (multiplier Λ ρ t) := by
  apply ((integrable_exp_neg_mul_sq ht).const_mul (Λ ^ (-ρ))).mono'
    (multiplier_continuous hΛ).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (multiplier_nonneg hΛ.le)]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos hΛ (by nlinarith : Λ ≤ Λ + x ^ (2 : ℕ)) (by linarith))
    (Real.exp_pos _).le

theorem multiplier_nat_summable {Λ ρ t : ℝ} (hΛ : 0 < Λ) (hρ : 0 ≤ ρ) (ht : 0 < t) :
    Summable (fun n : ℕ => multiplier Λ ρ t n) :=
  (multiplier_antitone hΛ hρ ht.le).summable_of_integrableOn_Ioi_zero
    (multiplier_integrable hΛ hρ ht).integrableOn (fun _ _ => multiplier_nonneg hΛ.le)

theorem multiplier_int_summable {Λ ρ t : ℝ} (hΛ : 0 < Λ) (hρ : 0 ≤ ρ) (ht : 0 < t) :
    Summable (fun n : ℤ => multiplier Λ ρ t n) := by
  have hn := multiplier_nat_summable hΛ hρ ht
  have hn' := (summable_nat_add_iff 1 (f := fun n : ℕ => multiplier Λ ρ t n)).mpr hn
  apply Summable.of_nat_of_neg_add_one (f := fun n : ℤ => multiplier Λ ρ t n) hn
  simpa only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, multiplier_even,
    Nat.cast_add, Nat.cast_one] using hn'

def fractionalGaussianIntegral (ρ : ℝ) := (1 / 2 : ℝ) * Real.Gamma ((1 - 2 * ρ) / 2)

theorem fractionalGaussianIntegral_pos {ρ : ℝ} (hρ : ρ < 1 / 2) :
    0 < fractionalGaussianIntegral ρ := by
  unfold fractionalGaussianIntegral
  exact mul_pos (by norm_num) (Real.Gamma_pos_of_pos (by linarith))

theorem fractional_gaussian_integral {ρ t : ℝ} (hρ : ρ < 1 / 2) (ht : 0 < t) :
    (∫ x in Ioi (0 : ℝ), x ^ (-2 * ρ) * Real.exp (-t * x ^ (2 : ℕ))) =
      fractionalGaussianIntegral ρ * t ^ (ρ - 1 / 2) := by
  have hh := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := -2 * ρ) (b := t)
    (by norm_num) (by linarith) ht
  simp only [Real.rpow_two] at hh
  rw [hh]
  have e₁ : -(-2 * ρ + 1) / 2 = ρ - 1 / 2 := by ring
  have e₂ : (-2 * ρ + 1) / 2 = (1 - 2 * ρ) / 2 := by ring
  rw [e₁, e₂]
  unfold fractionalGaussianIntegral
  ring

/-- Exact one-dimensional spectral heat trace, including the zero mode. -/
theorem centered_heat_trace_bound {Λ ρ t : ℝ}
    (hΛ : 1 ≤ Λ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1 / 2) (ht : 0 < t) :
    (∑' n : ℤ, multiplier Λ ρ t n) ≤
      1 + 2 * fractionalGaussianIntegral ρ * t ^ (ρ - 1 / 2) := by
  have hΛ0 : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hn := multiplier_nat_summable hΛ0 hρ0 ht
  have hanti := multiplier_antitone hΛ0 hρ0 ht.le
  have hint := hanti.tsum_add_one_le_integral
    (multiplier_integrable hΛ0 hρ0 ht).integrableOn (fun _ _ => multiplier_nonneg hΛ0.le)
  have hcompare : (∫ x in Ioi (0 : ℝ), multiplier Λ ρ t x) ≤
      fractionalGaussianIntegral ρ * t ^ (ρ - 1 / 2) := by
    rw [← fractional_gaussian_integral hρ1 ht]
    apply integral_mono_ae (multiplier_integrable hΛ0 hρ0 ht).integrableOn
      (integrableOn_rpow_mul_exp_neg_mul_sq ht (by linarith : -1 < -2 * ρ))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    unfold multiplier
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have he : x ^ (-2 * ρ) = (x ^ (2 : ℕ)) ^ (-ρ) := by
      rw [← Real.rpow_natCast_mul hx.le 2 (-ρ)]
      congr 1
      norm_num
    rw [he]
    exact Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hx)
      (by nlinarith : x ^ (2 : ℕ) ≤ Λ + x ^ (2 : ℕ)) (by linarith)
  have hzero : multiplier Λ ρ t 0 ≤ 1 := by
    simpa [multiplier] using Real.rpow_le_one_of_one_le_of_nonpos hΛ (by linarith : -ρ ≤ 0)
  have he : (∑' n : ℤ, multiplier Λ ρ t n) = multiplier Λ ρ t 0 +
      2 * ∑' n : ℕ, multiplier Λ ρ t (n + 1) := by
    have hn' := (summable_nat_add_iff 1 (f := fun n : ℕ => multiplier Λ ρ t n)).mpr hn
    have hneg : Summable (fun n : ℕ => (fun k : ℤ => multiplier Λ ρ t k) (-(n + 1))) := by
      simpa only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
        multiplier_even, Nat.cast_add, Nat.cast_one] using hn'
    rw [tsum_of_nat_of_neg_add_one (f := fun n : ℤ => multiplier Λ ρ t n) hn hneg]
    simp only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, multiplier_even]
    rw [hn.tsum_eq_zero_add]
    simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one, add_comm]
    ring
  rw [he]
  simp only [Nat.cast_add, Nat.cast_one] at hint
  nlinarith

theorem centered_heat_trace_small_time {Λ ρ t : ℝ}
    (hΛ : 1 ≤ Λ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1 / 2) (ht : 0 < t) (ht1 : t ≤ 1) :
    (∑' n : ℤ, multiplier Λ ρ t n) ≤
      (1 + 2 * fractionalGaussianIntegral ρ) * t ^ (ρ - 1 / 2) := by
  have hh := centered_heat_trace_bound hΛ hρ0 hρ1 ht
  have hp : 1 ≤ t ^ (ρ - 1 / 2) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1 (by linarith)
  nlinarith

theorem multiplier_le_of_sq_le {Λ ρ t x y : ℝ}
    (hΛ : 0 < Λ) (hρ : 0 ≤ ρ) (ht : 0 ≤ t) (hxy : x ^ (2 : ℕ) ≤ y ^ (2 : ℕ)) :
    multiplier Λ ρ t y ≤ multiplier Λ ρ t x := by
  unfold multiplier
  apply mul_le_mul
  · exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  · exact Real.exp_le_exp.mpr (by nlinarith)
  · exact (Real.exp_pos _).le
  · exact Real.rpow_nonneg (by positivity) _

theorem multiplier_le_mass {Λ ρ t x : ℝ} (hΛ : 0 < Λ) (hρ : 0 ≤ ρ) (ht : 0 ≤ t) :
    multiplier Λ ρ t x ≤ Λ ^ (-ρ) := by
  have hh := multiplier_le_of_sq_le (x := 0) (y := x) hΛ hρ ht (by simpa using sq_nonneg x)
  simpa [multiplier] using hh

theorem multiplier_mul_heat (Λ ρ t s x : ℝ) :
    multiplier Λ ρ t x * Real.exp (-s * x ^ (2 : ℕ)) = multiplier Λ ρ (t+s) x := by
  unfold multiplier
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Rearrangement proves the manuscript's heat-convolution inner sum is
uniform in the frequency of its physical input. No adapted Fourier
cancellation is used. -/
theorem shifted_heat_trace_le_centered {Λ ρ t s : ℝ}
    (hΛ : 0 < Λ) (hρ : 0 ≤ ρ) (ht : 0 ≤ t) (hs : 0 ≤ s) (hages : 0 < t+s)
    (j : ℤ) :
    (∑' k : ℤ, multiplier Λ ρ t k * Real.exp (-s * ((k-j : ℤ) : ℝ) ^ (2 : ℕ))) ≤
      ∑' k : ℤ, multiplier Λ ρ (t+s) k := by
  by_cases hs0 : s = 0
  · subst s
    simp
  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  let f : ℤ → ℝ := fun k => multiplier Λ ρ t k
  let g : ℤ → ℝ := fun k => Real.exp (-s * (k : ℝ) ^ (2 : ℕ))
  have hgs : Summable g := by
    simpa [g, multiplier] using multiplier_int_summable (Λ := 1) (ρ := 0) (t := s)
      (by norm_num) (by norm_num) hspos
  have hgshift : Summable (fun k => g (k-j)) :=
    hgs.comp_injective (fun a b hab => by omega)
  have hcross : Summable (fun k => f k * g (k-j)) := by
    apply Summable.of_nonneg_of_le (fun k => mul_nonneg (multiplier_nonneg hΛ.le) (Real.exp_pos _).le)
      (fun k => mul_le_mul_of_nonneg_right (multiplier_le_mass hΛ hρ ht) (Real.exp_pos _).le)
      (hgshift.mul_left (Λ ^ (-ρ)))
  have hdiag : Summable (fun k => f k * g k) := by
    simpa only [f, g, multiplier_mul_heat] using multiplier_int_summable hΛ hρ hages
  have horder : ∀ k l, 0 ≤ (f k - f l) * (g k - g l) := by
    intro k l
    by_cases hkl : (k : ℝ) ^ (2 : ℕ) ≤ (l : ℝ) ^ (2 : ℕ)
    · have hfkl := multiplier_le_of_sq_le hΛ hρ ht hkl
      have hgkl : g l ≤ g k := Real.exp_le_exp.mpr (by nlinarith)
      exact mul_nonneg (sub_nonneg.mpr hfkl) (sub_nonneg.mpr hgkl)
    · have hfkl := multiplier_le_of_sq_le hΛ hρ ht (le_of_lt (lt_of_not_ge hkl))
      have hgkl : g k ≤ g l := Real.exp_le_exp.mpr (by nlinarith)
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hfkl) (sub_nonpos.mpr hgkl)
  have hh := correlation_le_centered
    (f := f) (g := g)
    (by intro n; dsimp [f]; simp only [Int.cast_neg, multiplier_even])
    (by intro n; dsimp [g]; simp only [Int.cast_neg, neg_sq])
    horder j hdiag hcross
  simpa only [f, g, multiplier_mul_heat] using hh

/-- The full one-weight Fourier trace estimate before taking its square
root to obtain the Hilbert--Schmidt norm. -/
theorem one_weight_fourier_trace {Λ ρ t s : ℝ}
    (hΛ : 1 ≤ Λ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1 / 2)
    (ht : 0 ≤ t) (hs : 0 ≤ s) (hages : 0 < t+s) (hsmall : t+s ≤ 1) (j : ℤ) :
    (∑' k : ℤ, (Λ + (k : ℝ) ^ (2 : ℕ)) ^ (-ρ) *
      Real.exp (-t * (k : ℝ) ^ (2 : ℕ) - s * ((k-j : ℤ) : ℝ) ^ (2 : ℕ))) ≤
      (1 + 2 * fractionalGaussianIntegral ρ) * (t+s) ^ (ρ - 1 / 2) := by
  have hh := shifted_heat_trace_le_centered (lt_of_lt_of_le zero_lt_one hΛ) hρ0 ht hs hages j
  have htbound := centered_heat_trace_small_time hΛ hρ0 hρ1 hages hsmall
  apply le_trans _ htbound
  simpa only [multiplier, sub_eq_add_neg, Real.exp_add, neg_mul, mul_assoc] using hh

theorem shifted_heat_summable {Λ ρ t s : ℝ}
    (hΛ : 0 < Λ) (hρ : 0 ≤ ρ) (ht : 0 ≤ t) (hs : 0 ≤ s) (hages : 0 < t+s)
    (j : ℤ) :
    Summable (fun k : ℤ => multiplier Λ ρ t k * Real.exp (-s * ((k-j : ℤ) : ℝ) ^ (2 : ℕ))) := by
  by_cases hs0 : s = 0
  · subst s
    simpa using multiplier_int_summable hΛ hρ (by simpa using hages)
  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  have hg : Summable (fun k : ℤ => Real.exp (-s * (k : ℝ) ^ (2 : ℕ))) := by
    simpa [multiplier] using multiplier_int_summable (Λ := 1) (ρ := 0) (t := s)
      (by norm_num) (by norm_num) hspos
  have hgshift : Summable (fun k : ℤ => Real.exp (-s * ((k-j : ℤ) : ℝ) ^ (2 : ℕ))) :=
    hg.comp_injective (fun a b hab => by omega)
  exact Summable.of_nonneg_of_le
    (fun k => mul_nonneg (multiplier_nonneg hΛ.le) (Real.exp_pos _).le)
    (fun k => mul_le_mul_of_nonneg_right (multiplier_le_mass hΛ hρ ht) (Real.exp_pos _).le)
    (hgshift.mul_left (Λ ^ (-ρ)))

def matrixEnergy (Λ ρ t s : ℝ) (d : ℤ → ℂ) (kl : ℤ × ℤ) : ℝ :=
  ‖d (kl.1-kl.2)‖ ^ (2 : ℕ) * (Λ + (kl.1 : ℝ) ^ (2 : ℕ)) ^ (-ρ) *
    Real.exp (-t * (kl.1 : ℝ) ^ (2 : ℕ) - s * (kl.2 : ℝ) ^ (2 : ℕ))

/-- The genuine infinite Fourier-matrix square sum is finite and obeys
the one-input bound for every square-summable Fourier input. Identification
with a particular physical operator is deliberately separate. -/
theorem one_weight_matrix_energy {Λ ρ t s : ℝ}
    (hΛ : 1 ≤ Λ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1 / 2)
    (ht : 0 ≤ t) (hs : 0 ≤ s) (hages : 0 < t+s) (hsmall : t+s ≤ 1)
    (d : ℤ → ℂ) (hd : Summable (fun j => ‖d j‖ ^ (2 : ℕ))) :
    Summable (matrixEnergy Λ ρ t s d) ∧
      (∑' kl, matrixEnergy Λ ρ t s d kl) ≤
        ((1 + 2 * fractionalGaussianIntegral ρ) * (t+s) ^ (ρ - 1 / 2)) * ∑' j, ‖d j‖ ^ (2 : ℕ) := by
  let inner : ℤ → ℤ → ℝ := fun j k =>
    multiplier Λ ρ t k * Real.exp (-s * ((k-j : ℤ) : ℝ) ^ (2 : ℕ))
  let C : ℝ := (1 + 2 * fractionalGaussianIntegral ρ) * (t+s) ^ (ρ - 1 / 2)
  have hi : ∀ j, Summable (inner j) :=
    fun j => shifted_heat_summable (lt_of_lt_of_le zero_lt_one hΛ) hρ0 ht hs hages j
  have hi0 : ∀ j k, 0 ≤ inner j k := fun j k =>
    mul_nonneg (multiplier_nonneg (by linarith : 0 ≤ Λ)) (Real.exp_pos _).le
  have hiC : ∀ j, (∑' k, inner j k) ≤ C := by
    intro j
    have hh := one_weight_fourier_trace hΛ hρ0 hρ1 ht hs hages hsmall j
    simpa only [inner, C, multiplier, sub_eq_add_neg, Real.exp_add, neg_mul, mul_assoc] using hh
  have houter : Summable (fun j => ‖d j‖ ^ (2 : ℕ) * ∑' k, inner j k) :=
    Summable.of_nonneg_of_le
      (fun j => mul_nonneg (sq_nonneg _) (tsum_nonneg (hi0 j)))
      (fun j => mul_le_mul_of_nonneg_left (hiC j) (sq_nonneg _)) (hd.mul_right C)
  have hpair : Summable (fun jk : ℤ × ℤ => ‖d jk.1‖ ^ (2 : ℕ) * inner jk.1 jk.2) := by
    apply (summable_prod_of_nonneg (fun jk => mul_nonneg (sq_nonneg _) (hi0 jk.1 jk.2))).mpr
    constructor
    · exact fun j => (hi j).mul_left (‖d j‖ ^ (2 : ℕ))
    · simpa only [tsum_mul_left] using houter
  let e : (ℤ × ℤ) ≃ (ℤ × ℤ) :=
    { toFun := fun jk => (jk.2, jk.2-jk.1)
      invFun := fun kl => (kl.1-kl.2, kl.1)
      left_inv := by
        intro jk
        apply Prod.ext
        · dsimp
          ring
        · rfl
      right_inv := by
        intro kl
        apply Prod.ext
        · rfl
        · dsimp
          ring }
  have heq : (fun jk => matrixEnergy Λ ρ t s d (e jk)) =
      (fun jk : ℤ × ℤ => ‖d jk.1‖ ^ (2 : ℕ) * inner jk.1 jk.2) := by
    funext jk
    dsimp [matrixEnergy, e, inner, multiplier]
    rw [show jk.2 - (jk.2-jk.1) = jk.1 by ring]
    simp only [sub_eq_add_neg, Real.exp_add, neg_mul, mul_assoc]
  have hcomp : Summable (fun jk => matrixEnergy Λ ρ t s d (e jk)) := by
    rw [heq]
    exact hpair
  have hmatrix : Summable (matrixEnergy Λ ρ t s d) := e.summable_iff.mp hcomp
  refine ⟨hmatrix, ?_⟩
  calc
    _ = ∑' jk : ℤ × ℤ, ‖d jk.1‖ ^ (2 : ℕ) * inner jk.1 jk.2 := by
      rw [← e.tsum_eq (matrixEnergy Λ ρ t s d), heq]
    _ = ∑' j, ‖d j‖ ^ (2 : ℕ) * ∑' k, inner j k := by
      rw [hpair.tsum_prod]
      simp only [tsum_mul_left]
    _ ≤ ∑' j, ‖d j‖ ^ (2 : ℕ) * C :=
      houter.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left (hiC j) (sq_nonneg _)) (hd.mul_right C)
    _ = _ := by rw [tsum_mul_right]; exact mul_comm _ _

end SHE.HeatTrace
