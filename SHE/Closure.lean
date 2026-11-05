module

public import SHE.Parameters
public import SHE.Feedback

@[expose] public section

set_option autoImplicit false

/-! Conditional deterministic closure. The hypothesis below is a reduced
analytic estimate, and is NOT proved for solutions of the SPDE in this project.
In particular it must not be mistaken for a standard stochastic-calculus axiom. -/
noncomputable section
namespace SHE

def aGaussian (β : ℝ) := 1 / 2 - rho β
def aNative (β : ℝ) := 1 / 2 - rho β + 2 * (1 / 4) * qNative β 2
def aRemainder (β : ℝ) := 1 / 2 + 2 * (1 / 4) * (W β (depth β) - chiR β)

/-- The zero-loss reduced energy estimate after absorption and squaring.
Proving this for actual energies, with controlled losses and approximation
errors, is an outstanding analytic task, not an assumption about Ito calculus. -/
def ReducedMaster (β C Λ M : ℝ) : Prop :=
  M ≤ C * Λ ^ (-aGaussian β) * M ^ (alpha β) +
    C * Λ ^ (-aNative β) * M ^ (chi β) +
    C * Λ ^ (-aRemainder β) * M ^ (chiR β) + C * Λ ^ (-(5 / 2 : ℝ))

def closureConstant (β C : ℝ) :=
  (4 * C) ^ (1 / (1 - alpha β)) + (4 * C) ^ (1 / (1 - chi β)) +
    (4 * C) ^ (1 / (1 - chiR β)) + 4 * C

/-- The exact printed parameter family closes any instance of ReducedMaster. -/
theorem conditional_energy_closure {β C Λ M : ℝ}
    (hβ : 0 < β) (hsmall : β ≤ 4 / 25) (hC : 0 ≤ C)
    (hΛ : 1 ≤ Λ) (hM : 0 ≤ M) (hmaster : ReducedMaster β C Λ M) :
    M ≤ closureConstant β C * Λ ^ (-(5 / 2 : ℝ)) := by
  have had := admissible_parameters β hβ hsmall
  have hz₁ : alpha β < 1 := had.2.2.2.2.2.1
  have hz₂ : chi β < 1 := lt_of_lt_of_le had.2.2.2.2.2.2.2.1 (min_le_left _ _)
  have hz₃ : chiR β < 1 := lt_trans had.2.2.2.2.2.2.2.2.2 (by linarith : β < 1)
  have rates := all_rates_exceed_target β hβ hsmall
  have hb := three_row_decay hM hΛ hC
    (mul_nonneg hC (Real.rpow_nonneg (by linarith : 0 ≤ Λ) _)) hz₁ hz₂ hz₃ hmaster
  have hpow₁ : Λ ^ (-aGaussian β / (1 - alpha β)) ≤ Λ ^ (-(5 / 2 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hΛ
    rw [neg_div]
    dsimp [aGaussian]
    linarith [rates.1]
  have hpow₂ : Λ ^ (-aNative β / (1 - chi β)) ≤ Λ ^ (-(5 / 2 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hΛ
    rw [neg_div]
    dsimp [aNative]
    linarith [rates.2.1]
  have hpow₃ : Λ ^ (-aRemainder β / (1 - chiR β)) ≤ Λ ^ (-(5 / 2 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hΛ
    rw [neg_div]
    dsimp [aRemainder]
    linarith [rates.2.2]
  have hc₁ : 0 ≤ (4 * C) ^ (1 / (1 - alpha β)) := Real.rpow_nonneg (by positivity) _
  have hc₂ : 0 ≤ (4 * C) ^ (1 / (1 - chi β)) := Real.rpow_nonneg (by positivity) _
  have hc₃ : 0 ≤ (4 * C) ^ (1 / (1 - chiR β)) := Real.rpow_nonneg (by positivity) _
  have h₁ := mul_le_mul_of_nonneg_left hpow₁ hc₁
  have h₂ := mul_le_mul_of_nonneg_left hpow₂ hc₂
  have h₃ := mul_le_mul_of_nonneg_left hpow₃ hc₃
  dsimp [closureConstant]
  nlinarith

open Filter Topology in
theorem conditional_cost_limit {β C : ℝ} {M : ℝ → ℝ}
    (hβ : 0 < β) (hsmall : β ≤ 4 / 25) (hC : 0 ≤ C)
    (h : ∀ᶠ Λ in atTop, 1 ≤ Λ ∧ 0 ≤ M Λ ∧ ReducedMaster β C Λ (M Λ)) :
    Tendsto (fun Λ => Λ ^ (2 : ℕ) * M Λ) atTop (𝓝 0) := by
  apply damping_cost_tends_to_zero (p := (5 / 2 : ℝ)) (C := closureConstant β C) (by norm_num)
  filter_upwards [h] with Λ hΛ
  exact ⟨hΛ.2.1, conditional_energy_closure hβ hsmall hC hΛ.1 hΛ.2.1 hΛ.2.2⟩

end SHE
