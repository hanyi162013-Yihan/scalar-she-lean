module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic.BDGMomentAlgebra
open MeasureTheory

theorem add_power_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    (a + b) ^ n ≤ 2 ^ n * (a ^ n + b ^ n) := by
  rcases le_total a b with h | h
  · calc
      _ ≤ (2 * b) ^ n := pow_le_pow_left₀ (add_nonneg ha hb) (by linarith) n
      _ = 2 ^ n * b ^ n := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [pow_nonneg ha n]) (by positivity)
  · calc
      _ ≤ (2 * a) ^ n := pow_le_pow_left₀ (add_nonneg ha hb) (by linarith) n
      _ = 2 ^ n * a ^ n := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [pow_nonneg hb n]) (by positivity)

/-- The quadratic identity converts a moment of order 4p into a moment
of order 2p of its martingale term and its increasing term. -/
theorem square_power_le (p : ℕ) (x z a : ℝ) (ha : 0 ≤ a) (he : x ^ 2 = 2 * z + a) :
    ‖x‖ ^ (4 * p) ≤ ((2 : ℝ) ^ (2 * p)) ^ 2 * ‖z‖ ^ (2 * p) +
      (2 : ℝ) ^ (2 * p) * a ^ (2 * p) := by
  have hx : x ^ 2 ≤ 2 * |z| + a := by linarith [le_abs_self z]
  have hp := pow_le_pow_left₀ (sq_nonneg x) hx (2 * p)
  have hh := hp.trans (add_power_le (2 * |z|) a (by positivity) ha (2 * p))
  rw [show 4 * p = 2 * (2 * p) by omega, pow_mul, Real.norm_eq_abs, sq_abs]
  calc
    _ ≤ (2 : ℝ) ^ (2 * p) * ((2 : ℝ) ^ (2 * p) * |z| ^ (2 * p) + a ^ (2 * p)) := by
      simpa only [mul_pow] using hh
    _ = _ := by rw [Real.norm_eq_abs]; ring

theorem integral_square_power_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (p : ℕ) (X Z A : Ω → ℝ)
    (hA0 : ∀ ω, 0 ≤ A ω) (he : ∀ᵐ ω ∂μ, X ω ^ 2 = 2 * Z ω + A ω)
    (hX : Integrable (fun ω ↦ ‖X ω‖ ^ (4 * p)) μ)
    (hZ : Integrable (fun ω ↦ ‖Z ω‖ ^ (2 * p)) μ)
    (hA : Integrable (fun ω ↦ A ω ^ (2 * p)) μ) :
    (∫ ω, ‖X ω‖ ^ (4 * p) ∂μ) ≤ ((2 : ℝ) ^ (2 * p)) ^ 2 *
      (∫ ω, ‖Z ω‖ ^ (2 * p) ∂μ) + (2 : ℝ) ^ (2 * p) * ∫ ω, A ω ^ (2 * p) ∂μ := by
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add
    (hZ.const_mul _) (hA.const_mul _)]
  apply integral_mono_ae hX ((hZ.const_mul _).add (hA.const_mul _))
  filter_upwards [he] with ω hω
  exact square_power_le p (X ω) (Z ω) (A ω) (hA0 ω) hω

/-- The final absorption step in the moment-doubling estimate. -/
theorem absorb {a r k c : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) (hk : 0 ≤ k) (hc : 0 ≤ c)
    (h : a ≤ k * Real.sqrt a * Real.sqrt r + c * r) :
    a ≤ (2 * k ^ 2 + 2 * c) * r := by
  nlinarith [sq_nonneg (Real.sqrt a - k * Real.sqrt r), Real.sq_sqrt ha, Real.sq_sqrt hr,
    mul_nonneg (sq_nonneg k) hr]

end SHEStochastic.BDGMomentAlgebra
