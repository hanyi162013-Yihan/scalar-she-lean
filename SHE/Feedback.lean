module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

/-! Nonlinear feedback and decay after the analytic master estimate.
The estimate itself is not assumed to be a standard stochastic theorem. -/
noncomputable section
namespace SHE
open Filter Topology

theorem sublinear_bound {x A z : ℝ} (hx : 0 ≤ x) (hA : 0 ≤ A) (hz : z < 1)
    (h : x ≤ A * x ^ z) : x ≤ A ^ (1 / (1 - z)) := by
  by_cases hx0 : x = 0
  · subst x
    exact Real.rpow_nonneg hA _
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hp : 0 < 1 - z := sub_pos.mpr hz
  have hpow : x ^ (1 - z) ≤ A := by
    rw [Real.rpow_sub hxpos, Real.rpow_one]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hxpos z)).mpr h
  have hraise := Real.rpow_le_rpow (Real.rpow_nonneg hx _) hpow (le_of_lt (one_div_pos.mpr hp))
  rw [← Real.rpow_mul hx, mul_one_div_cancel (ne_of_gt hp), Real.rpow_one] at hraise
  exact hraise

/-- Quantitative feedback rate, including its constant. -/
theorem sublinear_decay {x c Λ a z : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c)
    (hΛ : 0 < Λ) (hz : z < 1)
    (h : x ≤ (c * Λ ^ (-a)) * x ^ z) :
    x ≤ c ^ (1 / (1 - z)) * Λ ^ (-a / (1 - z)) := by
  have hb := sublinear_bound hx (mul_nonneg hc (Real.rpow_nonneg hΛ.le _)) hz h
  rw [Real.mul_rpow hc (Real.rpow_nonneg hΛ.le _), ← Real.rpow_mul hΛ.le] at hb
  simpa [div_eq_mul_inv] using hb

/-- A four-way pigeonhole bound; the fourth slot is the deterministic error. -/
theorem four_slots {x a b c e : ℝ} (h : x ≤ a + b + c + e) :
    x ≤ 4 * a ∨ x ≤ 4 * b ∨ x ≤ 4 * c ∨ x ≤ 4 * e := by
  by_contra hn
  push Not at hn
  linarith [hn.1, hn.2.1, hn.2.2.1, hn.2.2.2]

/-- Three nonlinear rows plus the independent approximation error. -/
theorem three_row_decay {x Λ C a₁ a₂ a₃ z₁ z₂ z₃ e : ℝ}
    (hx : 0 ≤ x) (hΛ : 1 ≤ Λ) (hC : 0 ≤ C) (he : 0 ≤ e)
    (hz₁ : z₁ < 1) (hz₂ : z₂ < 1) (hz₃ : z₃ < 1)
    (h : x ≤ C * Λ ^ (-a₁) * x ^ z₁ + C * Λ ^ (-a₂) * x ^ z₂ +
      C * Λ ^ (-a₃) * x ^ z₃ + e) :
    x ≤ (4 * C) ^ (1 / (1 - z₁)) * Λ ^ (-a₁ / (1 - z₁)) +
      (4 * C) ^ (1 / (1 - z₂)) * Λ ^ (-a₂ / (1 - z₂)) +
      (4 * C) ^ (1 / (1 - z₃)) * Λ ^ (-a₃ / (1 - z₃)) + 4 * e := by
  have hΛpos : 0 < Λ := by linarith
  have h4C : 0 ≤ 4 * C := by positivity
  have hnon₁ : 0 ≤ (4 * C) ^ (1 / (1 - z₁)) * Λ ^ (-a₁ / (1 - z₁)) := by positivity
  have hnon₂ : 0 ≤ (4 * C) ^ (1 / (1 - z₂)) * Λ ^ (-a₂ / (1 - z₂)) := by positivity
  have hnon₃ : 0 ≤ (4 * C) ^ (1 / (1 - z₃)) * Λ ^ (-a₃ / (1 - z₃)) := by positivity
  rcases four_slots h with h₁ | h₂ | h₃ | h₄
  · have hi : x ≤ ((4 * C) * Λ ^ (-a₁)) * x ^ z₁ := by nlinarith [h₁]
    have hb := sublinear_decay hx h4C hΛpos hz₁ hi
    linarith
  · have hi : x ≤ ((4 * C) * Λ ^ (-a₂)) * x ^ z₂ := by nlinarith [h₂]
    have hb := sublinear_decay hx h4C hΛpos hz₂ hi
    linarith
  · have hi : x ≤ ((4 * C) * Λ ^ (-a₃)) * x ^ z₃ := by nlinarith [h₃]
    have hb := sublinear_decay hx h4C hΛpos hz₃ hi
    linarith
  · linarith

/-- A strict exponent margin survives a sufficiently small finite perturbation. -/
theorem rate_margin_stable {a z target : ℝ} (hz : z < 1)
    (ht : target < a / (1 - z)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, |δ| < ε → target < (a - δ) / (1 - z) := by
  have hp : 0 < 1 - z := sub_pos.mpr hz
  have hm : 0 < a - target * (1 - z) := by
    have := (lt_div_iff₀ hp).mp ht
    linarith
  refine ⟨(a - target * (1 - z)) / 2, by linarith, ?_⟩
  intro δ hδ
  apply (lt_div_iff₀ hp).mpr
  have := (abs_lt.mp hδ).2
  linarith

/-- Simultaneous losses in the damping numerator and in the nonlinear state
exponent can be chosen small enough after fixing the strict rate margin. -/
theorem joint_rate_losses_stable {a z target : ℝ} (hz : z < 1)
    (htarget : 0 ≤ target) (ht : target < a / (1 - z)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ η : ℝ, 0 ≤ δ → δ ≤ ε → 0 ≤ η → η ≤ ε →
      target < (a - δ) / (1 - (z - η)) := by
  have hp : 0 < 1 - z := sub_pos.mpr hz
  have hm : 0 < a - target * (1 - z) := by
    have := (lt_div_iff₀ hp).mp ht
    linarith
  let ε := (a - target * (1 - z)) / (2 * (1 + target))
  have hden : 0 < 2 * (1 + target) := by linarith
  have hε : 0 < ε := div_pos hm hden
  refine ⟨ε, hε, ?_⟩
  intro δ η hδ hδε hη hηε
  apply (lt_div_iff₀ (by linarith : 0 < 1 - (z - η))).mpr
  have he : 2 * (1 + target) * ε = a - target * (1 - z) := by
    dsimp [ε]
    field_simp
  have heη := mul_le_mul_of_nonneg_left hηε htarget
  nlinarith

/-- A linear row that loses a small state exponent also retains any fixed
target decay rate when its damping coefficient has a strict positive degree. -/
theorem linear_row_loss_stable {a target : ℝ} (ha : 0 < a) (ht : 0 ≤ target) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ η : ℝ, 0 < η → η < ε → target < a / η := by
  refine ⟨a / (target + 1), div_pos ha (by linarith), ?_⟩
  intro η hη hηε
  apply (lt_div_iff₀ hη).mpr
  have hm := (lt_div_iff₀ (by linarith : 0 < target + 1)).mp hηε
  nlinarith

/-- A damping-energy bound faster than Λ⁻² makes the Girsanov energy vanish. -/
theorem damping_cost_tends_to_zero {M : ℝ → ℝ} {C p : ℝ} (hp : 2 < p)
    (hM : ∀ᶠ Λ in atTop, 0 ≤ M Λ ∧ M Λ ≤ C * Λ ^ (-p)) :
    Tendsto (fun Λ => Λ ^ (2 : ℕ) * M Λ) atTop (𝓝 0) := by
  have hlim : Tendsto (fun Λ : ℝ => C * Λ ^ (-(p - 2))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by linarith : 0 < p - 2)).const_mul C
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [hM] with Λ h
    exact mul_nonneg (sq_nonneg Λ) h.1
  · filter_upwards [hM, eventually_gt_atTop (0 : ℝ)] with Λ h hΛ
    calc
      Λ ^ (2 : ℕ) * M Λ ≤ Λ ^ (2 : ℕ) * (C * Λ ^ (-p)) :=
        mul_le_mul_of_nonneg_left h.2 (sq_nonneg Λ)
      _ = C * Λ ^ (-(p - 2)) := by
        rw [← Real.rpow_natCast Λ 2]
        rw [mul_left_comm, ← Real.rpow_add hΛ]
        have he : (2 : ℝ) + -p = -(p - 2) := by ring
        rw [show (↑(2 : ℕ) : ℝ) = 2 by norm_num, he]

end SHE
