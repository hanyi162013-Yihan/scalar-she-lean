module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic.HeatIncrementRateAlgebra

theorem space_ratio {K S t d : ℝ} (hS : 0 < S) (ht : 0 < t) (hd : 0 ≤ d) :
    (d / Real.sqrt (t / S)) ^ (1 / 2 : ℝ) * (K * t ^ (-(1 / 2 : ℝ))) =
      (S ^ (1 / 4 : ℝ) * K) * d ^ (1 / 2 : ℝ) * t ^ (-(3 / 4 : ℝ)) := by
  have hh : 0 < t / S := div_pos ht hS
  rw [Real.div_rpow hd (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, ← Real.rpow_mul hh.le]
  norm_num only [show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num]
  have he : d ^ (1 / 2 : ℝ) / (t / S) ^ (1 / 4 : ℝ) =
      d ^ (1 / 2 : ℝ) * (t / S) ^ (-(1 / 4 : ℝ)) := by
    rw [Real.rpow_neg hh.le]
    rfl
  rw [he, Real.div_rpow ht.le hS.le, Real.rpow_neg hS.le, div_inv_eq_mul]
  calc
    _ = (S ^ (1 / 4 : ℝ) * K) * d ^ (1 / 2 : ℝ) *
        (t ^ (-(1 / 4 : ℝ)) * t ^ (-(1 / 2 : ℝ))) := by ring
    _ = _ := by rw [← Real.rpow_add ht]; norm_num

theorem time_ratio {K t δ : ℝ} (ht : 0 < t) (hδ : 0 ≤ δ) :
    ((δ / (t / 2)) ^ (1 / 8 : ℝ)) ^ 2 * (K * t ^ (-(1 / 2 : ℝ))) =
      (2 ^ (1 / 4 : ℝ) * K) * δ ^ (1 / 4 : ℝ) * t ^ (-(3 / 4 : ℝ)) := by
  have hh : 0 < t / 2 := by positivity
  rw [← Real.rpow_mul_natCast (div_nonneg hδ hh.le)]
  norm_num only [Nat.cast_ofNat, show (1 / 8 : ℝ) * 2 = 1 / 4 by norm_num]
  rw [Real.div_rpow hδ hh.le]
  have he : δ ^ (1 / 4 : ℝ) / (t / 2) ^ (1 / 4 : ℝ) =
      δ ^ (1 / 4 : ℝ) * (t / 2) ^ (-(1 / 4 : ℝ)) := by
    rw [Real.rpow_neg hh.le]
    rfl
  rw [he, Real.div_rpow ht.le (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
  calc
    _ = (2 ^ (1 / 4 : ℝ) * K) * δ ^ (1 / 4 : ℝ) *
        (t ^ (-(1 / 4 : ℝ)) * t ^ (-(1 / 2 : ℝ))) := by ring
    _ = _ := by rw [← Real.rpow_add ht]; norm_num

/-- Hölder interpolation preserves an integrable time singularity for
every β<1, while retaining a positive time-increment exponent. -/
theorem factorization {K t δ β : ℝ} (hK : 0 < K) (ht : 0 < t) (hδ : 0 ≤ δ) :
    (4 * (K * t ^ (-(1 / 2 : ℝ))) ^ 2) ^ β *
      (K * δ ^ (1 / 4 : ℝ) * t ^ (-(3 / 4 : ℝ))) ^ (1 - β) =
      4 ^ β * K ^ (1 + β) * δ ^ ((1 - β) / 4) * t ^ (-(3 + β) / 4) := by
  have hk : 0 ≤ K := hK.le
  have hd : 0 ≤ δ ^ (1 / 4 : ℝ) := Real.rpow_nonneg hδ _
  have hp : 0 ≤ K * t ^ (-(1 / 2 : ℝ)) := by positivity
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg _),
    ← Real.rpow_natCast_mul hp 2 β, Real.mul_rpow hk (Real.rpow_nonneg ht.le _),
    Real.mul_rpow (mul_nonneg hk hd) (Real.rpow_nonneg ht.le _), Real.mul_rpow hk hd,
    ← Real.rpow_mul ht.le, ← Real.rpow_mul hδ, ← Real.rpow_mul ht.le]
  calc
    _ = 4 ^ β * (K ^ (2 * β) * K ^ (1 - β)) * δ ^ ((1 / 4 : ℝ) * (1 - β)) *
        (t ^ (-(1 / 2 : ℝ) * (2 * β)) * t ^ (-(3 / 4 : ℝ) * (1 - β))) := by ring
    _ = _ := by
      rw [← Real.rpow_add hK, ← Real.rpow_add ht]
      congr 2 <;> ring

theorem leading_bound {K t δ β : ℝ} (hK : 1 ≤ K) (ht : 0 < t) (ht1 : t ≤ 1)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    K * δ ^ (1 / 4 : ℝ) * t ^ (-(3 / 4 : ℝ)) ≤
      4 ^ β * K ^ (1 + β) * δ ^ ((1 - β) / 4) * t ^ (-(3 + β) / 4) := by
  have hC : K ≤ 4 ^ β * K ^ (1 + β) := by
    have hk := Real.self_le_rpow_of_one_le hK (by linarith : 1 ≤ 1 + β)
    have h4 := Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 4) hβ
    nlinarith [Real.rpow_nonneg (by linarith : 0 ≤ K) (1 + β)]
  have hd := Real.rpow_le_rpow_of_exponent_ge' hδ hδ1
    (by linarith : 0 ≤ (1 - β) / 4) (by linarith : (1 - β) / 4 ≤ 1 / 4)
  have ht' := Real.rpow_le_rpow_of_exponent_ge ht ht1
    (by linarith : -(3 + β) / 4 ≤ -(3 / 4 : ℝ))
  exact mul_le_mul (mul_le_mul hC hd (by positivity) (by positivity)) ht'
    (by positivity) (by positivity)

end SHEStochastic.HeatIncrementRateAlgebra
