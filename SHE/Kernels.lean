module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false

/-! Two singular-endpoint calculations from the clipped time calculus.
These are scalar calculations; the multi-block convolution and all-offset
first-hit bounds are not claimed here. -/
noncomputable section
namespace SHE
open Set

def rootKernel (ν t : ℝ) := t ^ (-(1 : ℝ)) * min 1 (ν * t ^ (1 / 4 : ℝ))
def defectKernel (Λ s t : ℝ) := min 1 (Λ * t) * t ^ (-1 - s)

/-- The exact small-time root mass, retaining its vanishing at the corner. -/
theorem root_small_time_mass {ν h : ℝ} (hν : 0 ≤ ν) (hh : 0 ≤ h)
    (hcap : ν * h ^ (1 / 4 : ℝ) ≤ 1) :
    (∫ t in (0 : ℝ)..h, rootKernel ν t) = 4 * ν * h ^ (1 / 4 : ℝ) := by
  have heq : ∀ t ∈ Ioo (0 : ℝ) h, rootKernel ν t = ν * t ^ (-(3 / 4 : ℝ)) := by
    intro t ht
    have hc : ν * t ^ (1 / 4 : ℝ) ≤ 1 :=
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht.1.le ht.2.le (by norm_num)) hν).trans hcap
    unfold rootKernel
    rw [min_eq_right hc, mul_left_comm, ← Real.rpow_add ht.1]
    norm_num
  rw [intervalIntegral.integral_congr_Ioo_of_le hh heq, intervalIntegral.integral_const_mul]
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(3 / 4 : ℝ)))]
  norm_num
  ring

/-- Before the defect cutoff, its multiplier cancels one full time singularity. -/
theorem defect_small_time_mass {Λ s h : ℝ} (hΛ : 0 ≤ Λ) (hs : s < 1)
    (hh : 0 ≤ h) (hcap : Λ * h ≤ 1) :
    (∫ t in (0 : ℝ)..h, defectKernel Λ s t) = Λ * h ^ (1 - s) / (1 - s) := by
  have heq : ∀ t ∈ Ioo (0 : ℝ) h, defectKernel Λ s t = Λ * t ^ (-s) := by
    intro t ht
    have hc : Λ * t ≤ 1 := (mul_le_mul_of_nonneg_left ht.2.le hΛ).trans hcap
    unfold defectKernel
    rw [min_eq_right hc]
    calc
      Λ * t * t ^ (-1 - s) = Λ * (t ^ (1 : ℝ) * t ^ (-1 - s)) := by rw [Real.rpow_one]; ring
      _ = Λ * t ^ (-s) := by
        rw [← Real.rpow_add ht.1, show (1 : ℝ) + (-1 - s) = -s by ring]
  rw [intervalIntegral.integral_congr_Ioo_of_le hh heq, intervalIntegral.integral_const_mul]
  rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < -s))]
  have hz : -s + 1 ≠ 0 := by linarith
  rw [Real.zero_rpow hz, sub_zero]
  have he : -s + 1 = 1 - s := by ring
  rw [he]
  ring

/-- A cap can be weakened to any fractional power between zero and one. -/
theorem min_one_le_rpow {x θ : ℝ} (hx : 0 ≤ x) (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    min 1 x ≤ x ^ θ := by
  by_cases hsmall : x ≤ 1
  · rw [min_eq_right hsmall]
    by_cases hzero : x = 0
    · simp [hzero, Real.zero_rpow hθ.ne']
    have hpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hzero)
    simpa using Real.rpow_le_rpow_of_exponent_ge hpos hsmall hθ1
  · rw [min_eq_left (by linarith : 1 ≤ x)]
    exact Real.one_le_rpow (by linarith) hθ.le

end SHE
