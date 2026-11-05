module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

/-! Exact parameter arithmetic from Section 6 of the manuscript.
No stochastic or analytic estimate is assumed in this file. -/
noncomputable section
namespace SHE

def rho (β : ℝ) := 1 / 2 - 3 / 5 * β
def k (β : ℝ) := 3 * β
def alpha (β : ℝ) := β + 2 * rho β
def chi (β : ℝ) := 1 - 11 / 50 * β
def chiR (β : ℝ) := β / 2
def w (β : ℝ) (j : ℕ) := β + k β * (j - 1 : ℕ) * β / 4
def p (β : ℝ) (j : ℕ) := w β j - k β / 4
def qGamma (β : ℝ) := alpha β - k β * (1 - β) / 4
def qNative (β : ℝ) (j : ℕ) :=
  w β j + min (2 * rho β - chi β) (k β * (2 * rho β - chi β) / 4)
def qProfile (β : ℝ) (j : ℕ) := w β j + k β * rho β / 2 - k β / 4
def W (β : ℝ) (N : ℕ) := β + k β * N * β / 4
def depth (β : ℝ) : ℕ := ⌈6 / β ^ 2⌉₊

theorem rho_margin (β : ℝ) : 1 / 2 - rho β = 3 * β / 5 := by unfold rho; ring
theorem alpha_margin (β : ℝ) : 1 - alpha β = β / 5 := by unfold alpha rho; ring
theorem low_band_margin (β : ℝ) : 1 / 4 - (1 / 4) * (1 - β) = β / 4 := by ring
theorem qGamma_formula (β : ℝ) :
    qGamma β = 1 - 19 * β / 20 + 3 * β ^ 2 / 4 := by unfold qGamma alpha rho k; ring
theorem w_two (β : ℝ) : w β 2 = β + 3 * β ^ 2 / 4 := by norm_num [w, k]; ring
theorem p_two (β : ℝ) : p β 2 = β / 4 + 3 * β ^ 2 / 4 := by norm_num [p, w, k]; ring
theorem qProfile_two (β : ℝ) : qProfile β 2 = β - 3 * β ^ 2 / 20 := by
  norm_num [qProfile, w, k, rho]; ring
theorem chi_gap (β : ℝ) : alpha β - chi β = β / 50 := by unfold alpha rho chi; ring
theorem chi_margin (β : ℝ) : 1 - chi β = 11 * β / 50 := by unfold chi; ring

theorem qNative_two (β : ℝ) (hβ : 0 < β) (hsmall : β ≤ 4 / 25) :
    qNative β 2 = β / 50 + 3 * β ^ 2 / 4 := by
  have hm : 2 * rho β - chi β ≤ k β * (2 * rho β - chi β) / 4 := by
    unfold rho chi k
    have : 0 ≤ β ^ 2 := sq_nonneg β
    nlinarith
  rw [qNative, min_eq_left hm, w_two]
  unfold rho chi
  ring

theorem admissible_parameters (β : ℝ) (hβ : 0 < β) (hsmall : β ≤ 4 / 25) :
    0 < rho β ∧ rho β < 1 / 2 ∧ 0 < k β ∧ k β < 4 ∧
    0 < alpha β ∧ alpha β < 1 ∧ 0 < chi β ∧ chi β < min 1 (alpha β) ∧
    0 < chiR β ∧ chiR β < β := by
  dsimp [rho, k, alpha, chi, chiR]
  rw [lt_min_iff]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · constructor <;> linarith
  constructor <;> linarith

theorem all_degrees_positive (β : ℝ) (hβ : 0 < β) (hsmall : β ≤ 4 / 25) :
    0 < qGamma β ∧ 0 < w β 2 ∧ 0 < p β 2 ∧
    0 < qProfile β 2 ∧ 0 < qNative β 2 := by
  rw [qGamma_formula, w_two, p_two, qProfile_two, qNative_two β hβ hsmall]
  have hs : β ^ 2 ≤ (4 / 25) * β := by nlinarith
  have hsq : 0 ≤ β ^ 2 := sq_nonneg β
  constructor
  · nlinarith
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · nlinarith
  positivity

theorem p_increases (β : ℝ) (j : ℕ) (hj : 1 ≤ j) :
    p β (j + 1) - p β j = 3 * β ^ 2 / 4 := by
  have hn : j + 1 - 1 = (j - 1) + 1 := by omega
  simp only [p, w, k, hn, Nat.cast_add, Nat.cast_one]
  ring

theorem all_predictable_degrees_positive (β : ℝ) (hβ : 0 < β)
    (j : ℕ) (hj : 2 ≤ j) : 0 < p β j := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hj
  have he : p β (2 + n) = β / 4 + 3 * β ^ 2 / 4 + 3 * β ^ 2 / 4 * n := by
    norm_num [p, w, k, Nat.add_sub_assoc]
    ring
  rw [he]
  positivity

theorem depth_lower (β : ℝ) : 6 / β ^ 2 ≤ (depth β : ℝ) := Nat.le_ceil _

theorem depth_at_least_two (β : ℝ) (hβ : 0 < β) (hsmall : β ≤ 4 / 25) :
    2 ≤ depth β := by
  have hsq : 0 < β ^ 2 := sq_pos_of_pos hβ
  have hprod := (div_le_iff₀ hsq).mp (depth_lower β)
  by_contra hn
  have hn' : (depth β : ℝ) ≤ 1 := by exact_mod_cast (show depth β ≤ 1 by omega)
  have : β ^ 2 < 1 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hn' (le_of_lt hsq)]

theorem remainder_depth (β : ℝ) (hβ : 0 < β) :
    β + 9 / 2 ≤ W β (depth β) := by
  have hsq : 0 < β ^ 2 := sq_pos_of_pos hβ
  have hprod := (div_le_iff₀ hsq).mp (depth_lower β)
  unfold W k
  nlinarith

theorem gaussian_rate (β : ℝ) (hβ : 0 < β) :
    (1 / 2 - rho β) / (1 - alpha β) = 3 := by
  rw [rho_margin, alpha_margin]
  field_simp

theorem native_rate (β : ℝ) (hβ : 0 < β) (hsmall : β ≤ 4 / 25) :
    (1 / 2 - rho β + 2 * (1 / 4) * qNative β 2) / (1 - chi β) =
      61 / 22 + 75 * β / 44 := by
  rw [rho_margin, qNative_two β hβ hsmall, chi_margin]
  field_simp
  nlinarith

theorem remainder_rate_lower (β : ℝ) (hβ : 0 < β) (hsmall : β ≤ 4 / 25) :
    11 / 4 < (1 / 2 + 2 * (1 / 4) * (W β (depth β) - chiR β)) / (1 - chiR β) := by
  have hw := remainder_depth β hβ
  unfold chiR
  apply (lt_div_iff₀ (by linarith : 0 < 1 - β / 2)).mpr
  nlinarith

theorem all_rates_exceed_target (β : ℝ) (hβ : 0 < β) (hsmall : β ≤ 4 / 25) :
    5 / 2 < (1 / 2 - rho β) / (1 - alpha β) ∧
    5 / 2 < (1 / 2 - rho β + 2 * (1 / 4) * qNative β 2) / (1 - chi β) ∧
    5 / 2 < (1 / 2 + 2 * (1 / 4) * (W β (depth β) - chiR β)) / (1 - chiR β) := by
  rw [gaussian_rate β hβ, native_rate β hβ hsmall]
  have hr := remainder_rate_lower β hβ hsmall
  constructor
  · norm_num
  constructor <;> linarith

/-- An effective exponent exists for every positive original exponent. -/
theorem effective_exponent (β₀ : ℝ) (h : 0 < β₀) :
    ∃ β : ℝ, 0 < β ∧ β ≤ β₀ ∧ β ≤ 4 / 25 := by
  refine ⟨min β₀ (4 / 25), lt_min h (by norm_num), min_le_left _ _, min_le_right _ _⟩

end SHE
