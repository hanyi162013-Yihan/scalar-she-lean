module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

/-! Scalar two-child weighted Haar calculation and lowering a Hölder exponent.
This is the local algebra behind the Haar columns, not the infinite-dimensional
transport or derivative estimates. -/
noncomputable section
namespace SHE

def haarMass (l r : ℝ) := Real.sqrt (l * r / (l + r))
def haarLeft (l r : ℝ) := haarMass l r / l
def haarRight (l r : ℝ) := -haarMass l r / r

theorem haar_cancellation {l r : ℝ} (hl : 0 < l) (hr : 0 < r) :
    l * haarLeft l r + r * haarRight l r = 0 := by
  unfold haarLeft haarRight
  field_simp
  ring

theorem haar_normalization {l r : ℝ} (hl : 0 < l) (hr : 0 < r) :
    l * (haarLeft l r) ^ 2 + r * (haarRight l r) ^ 2 = 1 := by
  have hsq : (haarMass l r) ^ 2 = l * r / (l + r) := by
    unfold haarMass
    apply Real.sq_sqrt
    positivity
  unfold haarLeft haarRight
  field_simp
  have hm : (l + r) * (haarMass l r) ^ 2 = l * r := by
    rw [hsq]
    field_simp
  nlinarith

/-- The positive half coefficient agrees with the formula printed in the paper. -/
theorem haarLeft_formula {l r : ℝ} (hl : 0 < l) (hr : 0 < r) :
    haarLeft l r = Real.sqrt (r / (l * (l + r))) := by
  have hL : 0 ≤ haarLeft l r := by unfold haarLeft haarMass; positivity
  have hsq : (haarLeft l r) ^ 2 = r / (l * (l + r)) := by
    unfold haarLeft haarMass
    rw [div_pow, Real.sq_sqrt (by positivity)]
    field_simp
  rw [← hsq, Real.sqrt_sq hL]

/-- Lower a bounded coefficient's exponent using the small/large-distance split. -/
theorem bounded_holder_lowering {d β β₀ L B δ : ℝ}
    (hd : 0 ≤ d) (hβ : 0 < β) (hββ : β ≤ β₀)
    (hL : 0 ≤ L) (hB : 0 ≤ B) (hδ : δ ≤ L * d ^ β₀) (hbound : δ ≤ B) :
    δ ≤ max L B * d ^ β := by
  by_cases hd1 : d ≤ 1
  · by_cases hd0 : d = 0
    · subst d
      have hβ₀ : β₀ ≠ 0 := by linarith
      simpa [Real.zero_rpow hβ.ne', Real.zero_rpow hβ₀] using hδ
    have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
    have hp := Real.rpow_le_rpow_of_exponent_ge hdpos hd1 hββ
    calc
      δ ≤ L * d ^ β₀ := hδ
      _ ≤ L * d ^ β := mul_le_mul_of_nonneg_left hp hL
      _ ≤ max L B * d ^ β := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hd _)
  · have hdge : 1 ≤ d := by linarith
    have hp : 1 ≤ d ^ β := Real.one_le_rpow hdge hβ.le
    calc
      δ ≤ B := hbound
      _ ≤ B * d ^ β := by nlinarith
      _ ≤ max L B * d ^ β := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hd _)

end SHE
