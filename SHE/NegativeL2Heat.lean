module

public import SHE.NegativeNash

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NegativeL2Heat
open MeasureTheory CircleHeat NegativeNash

theorem fractional_exp_bound {u ρ : ℝ} (hu : 0 ≤ u) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    u^ρ*Real.exp (-u) ≤ 1 := by
  have he : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  by_cases hu1 : u ≤ 1
  · exact (mul_le_mul (Real.rpow_le_one hu hu1 hρ) he (Real.exp_nonneg _) zero_le_one).trans_eq (by norm_num)
  · have hp : u^ρ ≤ u := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hu1) hρ1
    have hb := mul_le_mul_of_nonneg_right hp (Real.exp_nonneg (-u))
    exact hb.trans ((Real.mul_exp_neg_le_exp_neg_one u).trans
      (Real.exp_le_one_iff.mpr (by norm_num)))

theorem polynomial_heat_bound {t k ρ : ℝ} (ht : 0 < t) (hk : 0 ≤ k)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    k^ρ*Real.exp (-t*k) ≤ t^(-ρ) := by
  have hb := fractional_exp_bound (mul_nonneg ht.le hk) hρ hρ1
  rw [Real.mul_rpow ht.le hk] at hb
  have hp : 0 < t^ρ := Real.rpow_pos_of_pos ht _
  have he : t^ρ*t^(-ρ)=1 := by rw [← Real.rpow_add ht]; simp
  apply (mul_le_mul_iff_right₀ hp).mp
  calc
    _ = (t^ρ*k^ρ)*Real.exp (-(t*k)) := by rw [neg_mul]; ring
    _ ≤ 1 := by simpa only [neg_mul] using hb
    _ = _ := he.symm

theorem multiplier_bound {Λ ρ t : ℝ} (hΛ : 0 < Λ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (ht : 0 < t) (n : ℤ) :
    (Λ+(n:ℝ)^2)^ρ*‖heatWeight t n‖^2 ≤ Λ^ρ+t^(-ρ) := by
  have hw0 : 0 ≤ ‖heatWeight t n‖^2 := sq_nonneg _
  have hw1 : ‖heatWeight t n‖^2 ≤ 1 := by
    have hn := heatWeight_norm_le t n
    nlinarith [norm_nonneg (heatWeight t n)]
  have hpi : 1 ≤ 8*Real.pi^2 := by nlinarith [Real.two_le_pi]
  have hw : ‖heatWeight t n‖^2 ≤ Real.exp (-t*(n:ℝ)^2) := by
    rw [heatWeight_norm_sq ht.le]
    apply Real.exp_le_exp.mpr
    have hh := mul_nonneg (sub_nonneg.mpr hpi) (mul_nonneg ht.le (sq_nonneg (n:ℝ)))
    nlinarith only [hh]
  have hp := polynomial_heat_bound ht (sq_nonneg (n:ℝ)) hρ hρ1
  have hs := Real.rpow_add_le_add_rpow hΛ.le (sq_nonneg (n:ℝ)) hρ hρ1
  calc
    _ ≤ (Λ^ρ+((n:ℝ)^2)^ρ)*‖heatWeight t n‖^2 := mul_le_mul_of_nonneg_right hs hw0
    _ = Λ^ρ*‖heatWeight t n‖^2+((n:ℝ)^2)^ρ*‖heatWeight t n‖^2 := by ring
    _ ≤ Λ^ρ*1+((n:ℝ)^2)^ρ*Real.exp (-t*(n:ℝ)^2) :=
      add_le_add (mul_le_mul_of_nonneg_left hw1 (Real.rpow_nonneg hΛ.le _))
        (mul_le_mul_of_nonneg_left hw (Real.rpow_nonneg (sq_nonneg _) _))
    _ ≤ _ := by simpa only [mul_one] using add_le_add_right hp (Λ^ρ)

/-- Actual massive negative-input L² heat smoothing on the unit circle,
with constant one and the literal Fourier negative energy. -/
theorem heat_norm_sq_negative {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (ht : 0 < t) (v : CircleL2) :
    ‖heat t v‖^2 ≤ (Λ^ρ+t^(-ρ))*energy Λ ρ v := by
  have hΛ0 := zero_lt_one.trans_le hΛ
  have hc (n : ℤ) : ‖fourierCoeff (heat t v) n‖^2 ≤
      (Λ^ρ+t^(-ρ))*((Λ+(n:ℝ)^2)^(-ρ)*‖fourierCoeff v n‖^2) := by
    rw [heat_fourierCoeff,norm_mul,mul_pow]
    have hz : 0 < Λ+(n:ℝ)^2 := by positivity
    have hzpow : 0 < (Λ+(n:ℝ)^2)^ρ := Real.rpow_pos_of_pos hz _
    have hb := multiplier_bound hΛ0 hρ hρ1 ht n
    have he : (Λ+(n:ℝ)^2)^ρ*(Λ+(n:ℝ)^2)^(-ρ)=1 := by
      rw [← Real.rpow_add hz]; simp
    have hh : ‖heatWeight t n‖^2 ≤ (Λ^ρ+t^(-ρ))*(Λ+(n:ℝ)^2)^(-ρ) := by
      apply (mul_le_mul_iff_right₀ hzpow).mp
      calc
        _ ≤ Λ^ρ+t^(-ρ) := hb
        _ = _ := by rw [mul_left_comm,he,mul_one]
    exact (mul_le_mul_of_nonneg_right hh (sq_nonneg _)).trans_eq (by ring)
  have hs := (summable_fourier_sq (heat t v)).tsum_le_tsum hc
    ((energy_summable hΛ0 hρ v).mul_left (Λ^ρ+t^(-ρ)))
  simpa only [← norm_sq_fourier,tsum_mul_left,energy] using hs

end SHE.NegativeL2Heat
