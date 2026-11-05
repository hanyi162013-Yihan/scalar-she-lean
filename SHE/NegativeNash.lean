module

public import SHE.HeatMarkov

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.NegativeNash
open Finset Set MeasureTheory AddCircle CircleHeat HeatMarkov
local instance negativeNash_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

def energy (Λ ρ : ℝ) (f : CircleL2) : ℝ :=
  ∑' n : ℤ, (Λ+(n:ℝ)^2)^(-ρ) * ‖fourierCoeff f n‖^2

theorem energy_summable {Λ ρ : ℝ} (hΛ : 0 < Λ) (hρ : 0 ≤ ρ) (f : CircleL2) :
    Summable (fun n : ℤ => (Λ+(n:ℝ)^2)^(-ρ) * ‖fourierCoeff f n‖^2) := by
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ ((summable_fourier_sq f).mul_left (Λ^(-ρ)))
  intro n
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos hΛ (le_add_of_nonneg_right (sq_nonneg _)) (by linarith)) (sq_nonneg _)

theorem energy_eq_negativeEnergy (Λ ρ : ℝ) (hΛ : 0 < Λ) (f : CircleL2) :
    energy Λ ρ f = StepInput.negativeEnergy 1 Λ ρ f := by
  unfold energy StepInput.negativeEnergy weightedFourierSq massiveWeight
  apply tsum_congr
  intro n
  simp only [one_mul]
  rw [Real.rpow_neg (by positivity : 0 ≤ Λ+(n:ℝ)^2)]

theorem min_one_le_rpow {u ρ : ℝ} (hu : 0 ≤ u) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    min 1 u ≤ u^ρ := by
  by_cases hu1 : u ≤ 1
  · rw [min_eq_right hu1]
    exact Real.self_le_rpow_of_le_one hu hu1 hρ1
  · rw [min_eq_left (le_of_not_ge hu1)]
    exact Real.one_le_rpow (le_of_not_ge hu1) hρ0

theorem high_cutoff_weight {Λ ρ ε : ℝ} (hΛ : 0 < Λ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hε : 0 < ε) (n : ℤ) :
    (Λ+(n:ℝ)^2)^(-ρ) * (1-Real.exp (-ε*(n:ℝ)^2)) ≤ ε^ρ := by
  let z : ℝ := Λ+(n:ℝ)^2
  have hz : 0 < z := by dsimp [z]; positivity
  have hdiff : 1-Real.exp (-ε*(n:ℝ)^2) ≤ min 1 (ε*z) := by
    apply le_min
    · linarith [Real.exp_pos (-ε*(n:ℝ)^2)]
    · have hh := Real.add_one_le_exp (-ε*(n:ℝ)^2)
      dsimp only [z]
      nlinarith [mul_pos hε hΛ]
  have hh := hdiff.trans (min_one_le_rpow (by positivity : 0 ≤ ε*z) hρ0 hρ1)
  have hb := mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hz.le (-ρ))
  apply hb.trans_eq
  rw [Real.mul_rpow hε.le hz.le]
  calc
    _ = ε^ρ * (z^(-ρ)*z^ρ) := by ring
    _ = ε^ρ := by rw [← Real.rpow_add hz]; simp

def interpolationConstant (ρ : ℝ) : ℝ := 2 + 2*HeatTrace.fractionalGaussianIntegral ρ

theorem energy_cutoff {Λ ρ ε : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (f : CircleL2) :
    energy Λ ρ f ≤ (1+2*HeatTrace.fractionalGaussianIntegral ρ) *
      ε^(ρ-1/2) * normOne f^2 + ε^ρ*‖f‖^2 := by
  have hΛ0 : 0 < Λ := zero_lt_one.trans_le hΛ
  have hL := normOne_nonneg f
  have hmajor (n : ℤ) : (Λ+(n:ℝ)^2)^(-ρ)*‖fourierCoeff f n‖^2 ≤
      normOne f^2 * HeatTrace.multiplier Λ ρ ε n + ε^ρ*‖fourierCoeff f n‖^2 := by
    let w : ℝ := (Λ+(n:ℝ)^2)^(-ρ)
    let e : ℝ := Real.exp (-ε*(n:ℝ)^2)
    have hw : 0 ≤ w := by dsimp [w]; positivity
    have he : 0 ≤ e := (Real.exp_pos _).le
    have hc := pow_le_pow_left₀ (norm_nonneg _) (fourierCoeff_norm_le_normOne f n) 2
    have hlow := mul_le_mul_of_nonneg_left hc (mul_nonneg hw he)
    have hhigh := mul_le_mul_of_nonneg_right
      (high_cutoff_weight hΛ0 hρ.le (by linarith : ρ ≤ 1) hε n) (sq_nonneg ‖fourierCoeff f n‖)
    change w*(1-e)*‖fourierCoeff f n‖^2 ≤ ε^ρ*‖fourierCoeff f n‖^2 at hhigh
    dsimp only [HeatTrace.multiplier]
    change w*‖fourierCoeff f n‖^2 ≤ normOne f^2*(w*e)+ε^ρ*‖fourierCoeff f n‖^2
    nlinarith only [hlow,hhigh]
  have ht := HeatTrace.multiplier_int_summable hΛ0 hρ.le hε
  have hc : 1 ≤ ε^(ρ-1/2) := by
    simpa using Real.rpow_le_rpow_of_nonpos hε hε1 (by linarith : ρ-1/2 ≤ 0)
  calc
    _ ≤ ∑' n : ℤ, (normOne f^2*HeatTrace.multiplier Λ ρ ε n + ε^ρ*‖fourierCoeff f n‖^2) :=
      (energy_summable hΛ0 hρ.le f).tsum_le_tsum hmajor ((ht.mul_left _).add ((summable_fourier_sq f).mul_left _))
    _ = normOne f^2*(∑' n : ℤ, HeatTrace.multiplier Λ ρ ε n) + ε^ρ*‖f‖^2 := by
      rw [Summable.tsum_add (ht.mul_left _) ((summable_fourier_sq f).mul_left _),
        tsum_mul_left, tsum_mul_left, ← norm_sq_fourier]
    _ ≤ normOne f^2*(1+2*HeatTrace.fractionalGaussianIntegral ρ*ε^(ρ-1/2)) + ε^ρ*‖f‖^2 :=
      add_le_add (mul_le_mul_of_nonneg_left
        (HeatTrace.centered_heat_trace_bound hΛ hρ.le hρhalf hε) (sq_nonneg _)) le_rfl
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg (normOne f))]

/-- Actual negative Sobolev interpolation on the circle. The proof uses
the complete Fourier coefficients, a Gaussian low-frequency cutoff, and
the exact lattice heat trace. It applies to arbitrary complex `L²` data. -/
theorem energy_interpolation {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (f : CircleL2) : energy Λ ρ f ≤ interpolationConstant ρ *
      ‖f‖^(2-4*ρ) * (normOne f)^(4*ρ) := by
  by_cases hf : f = 0
  · subst f
    have hc (n : ℤ) : fourierCoeff (0 : CircleL2) n = 0 := by
      rw [← fourierBasis_repr, map_zero]
      rfl
    simp only [energy, hc, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, tsum_zero]
    have hI : 0 ≤ interpolationConstant ρ := by
      have hG := (HeatTrace.fractionalGaussianIntegral_pos hρhalf).le
      unfold interpolationConstant
      positivity
    exact mul_nonneg (mul_nonneg hI (Real.rpow_nonneg (by norm_num) _))
      (Real.rpow_nonneg (normOne_nonneg _) _)
  have hX : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hY : 0 < normOne f := normOne_pos_of_ne_zero f hf
  let r : ℝ := normOne f / ‖f‖
  have hr : 0 < r := div_pos hY hX
  have hr1 : r ≤ 1 := (div_le_one hX).mpr (normOne_le_norm f)
  have hε : 0 < r^4 := pow_pos hr _
  have hε1 : r^4 ≤ 1 := pow_le_one₀ hr.le hr1
  have hbalance1 : (r^4)^(ρ-1/2) * normOne f^2 = r^(4*ρ)*‖f‖^2 := by
    have he : normOne f = r*‖f‖ := by dsimp only [r]; field_simp
    rw [← Real.rpow_natCast_mul hr.le, he, mul_pow]
    norm_num only [Nat.cast_ofNat]
    calc
      _ = (r^((4:ℝ)*(ρ-1/2)) * r^(2:ℝ)) * ‖f‖^2 := by rw [Real.rpow_two]; ring
      _ = _ := by rw [← Real.rpow_add hr, show (4:ℝ)*(ρ-1/2)+2 = 4*ρ by ring]
  have hbalance2 : (r^4)^ρ*‖f‖^2 = r^(4*ρ)*‖f‖^2 := by rw [← Real.rpow_natCast_mul hr.le]; norm_num
  have hh := energy_cutoff hΛ hρ hρhalf hε hε1 f
  rw [mul_assoc, hbalance1, hbalance2] at hh
  have he : ‖f‖^2*r^(4*ρ) = ‖f‖^(2-4*ρ)*(normOne f)^(4*ρ) := by
    dsimp only [r]
    rw [Real.div_rpow hY.le hX.le]
    calc
      _ = (‖f‖^(2:ℝ)/‖f‖^(4*ρ))*(normOne f)^(4*ρ) := by rw [Real.rpow_two]; ring
      _ = _ := by rw [← Real.rpow_sub hX]
  apply hh.trans_eq
  calc
    _ = interpolationConstant ρ * (‖f‖^2*r^(4*ρ)) := by unfold interpolationConstant; ring
    _ = _ := by rw [he]; ring

end SHE.NegativeNash
