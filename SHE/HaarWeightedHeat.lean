module

public import SHE.NegativeNash
public import SHE.DyadicPowerSeries

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.HaarWeightedHeat
open Finset Set MeasureTheory AddCircle CircleHeat FiniteHaar HeatMarkov NegativeNash
open scoped ENNReal
local instance haarWeightedHeat_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

def besselHalf (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) : CircleL2 →L[ℂ] CircleL2 :=
  CircleNormalization.push.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((OneInputOperator.besselHalf Λ ρ hΛ hρ).comp
      CircleNormalization.push.toLinearIsometry.toContinuousLinearMap)

theorem besselHalf_norm_sq (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (f : CircleL2) :
    ‖besselHalf Λ ρ hΛ hρ f‖^2 = energy Λ ρ f := by
  change ‖CircleNormalization.push.symm (OneInputOperator.besselHalf Λ ρ hΛ hρ
    (CircleNormalization.push f))‖^2 = _
  rw [CircleNormalization.push.symm.norm_map, CircleNormalization.push_bessel_energy hΛ hρ,
    energy_eq_negativeEnergy Λ ρ (zero_lt_one.trans_le hΛ)]

theorem interpolationConstant_nonneg {ρ : ℝ} (hρhalf : ρ < 1/2) : 0 ≤ interpolationConstant ρ := by
  have hG := (HeatTrace.fractionalGaussianIntegral_pos hρhalf).le
  unfold interpolationConstant
  positivity

theorem energy_square_bounds {Λ ρ H L C : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (hC : 0 ≤ C) (u : CircleL2)
    (hu : ‖u‖^2 ≤ H*C) (hu1 : normOne u^2 ≤ L*C) :
    energy Λ ρ u ≤ interpolationConstant ρ * H^(1-2*ρ) * L^(2*ρ) * C := by
  have hp : 0 < 1-2*ρ := by linarith
  have hq : 0 < 2*ρ := by linarith
  have he : ‖u‖^(2-4*ρ) = (‖u‖^2)^(1-2*ρ) := by
    rw [← Real.rpow_natCast_mul (norm_nonneg u)]
    congr 1
    norm_num
    ring
  have he1 : normOne u^(4*ρ) = (normOne u^2)^(2*ρ) := by
    rw [← Real.rpow_natCast_mul (normOne_nonneg u)]
    congr 1
    norm_num
    ring
  calc
    _ ≤ interpolationConstant ρ * (‖u‖^2)^(1-2*ρ) * (normOne u^2)^(2*ρ) := by
      simpa only [he,he1] using energy_interpolation hΛ hρ hρhalf u
    _ ≤ interpolationConstant ρ * (H*C)^(1-2*ρ) * (L*C)^(2*ρ) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (sq_nonneg _) hu hp.le)
        (interpolationConstant_nonneg hρhalf))
        (Real.rpow_le_rpow (sq_nonneg _) hu1 hq.le) (Real.rpow_nonneg (sq_nonneg _) _)
        (mul_nonneg (interpolationConstant_nonneg hρhalf) (Real.rpow_nonneg (mul_nonneg hH hC) _))
    _ = _ := by
      rw [Real.mul_rpow hH hC, Real.mul_rpow hL hC]
      calc
        _ = interpolationConstant ρ * H^(1-2*ρ) * L^(2*ρ) * (C^(1-2*ρ)*C^(2*ρ)) := by ring
        _ = _ := by
          rw [← Real.rpow_add' hC (by linarith : 1-2*ρ+2*ρ ≠ 0),
            show 1-2*ρ+2*ρ = 1 by ring, Real.rpow_one]

theorem multiply_normOne_le (b : CircleL2) (B : ℝ)
    (hb : ∀ᵐ y ∂haarAddCircle, ‖b y‖ ≤ B) (u : CircleL2) :
    normOne (CircleMultiplier.operator b B hb u) ≤ B*normOne u := by
  have hi (v : CircleL2) : Integrable (v : AddCircle (1:ℝ) → ℂ) haarAddCircle :=
    (Lp.memLp v).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  unfold normOne
  rw [← integral_const_mul]
  apply integral_mono_ae (hi _).norm ((hi u).norm.const_mul B)
  filter_upwards [CircleMultiplier.operator_ae b B hb u,hb] with y hy hb
  rw [hy,norm_mul]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

def packetConstant (ρ : ℝ) : ℝ := interpolationConstant ρ * packetHeatConstant^(1-2*ρ)

theorem packetConstant_nonneg {ρ : ℝ} (hρhalf : ρ < 1/2) : 0 ≤ packetConstant ρ :=
  mul_nonneg (interpolationConstant_nonneg hρhalf) (Real.rpow_nonneg (zero_le_one.trans packetHeatConstant_one_le) _)

/-- A bounded, arbitrarily rough output multiplier retains the exact
negative Sobolev packet gain. The input is the actual periodic `L²`
packet and the Bessel operator uses the complete Fourier basis. -/
theorem weighted_packet {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (ht : 0 < t) (ht1 : t ≤ 1) (p : List Bool) (v b : CircleL2) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ᵐ y ∂haarAddCircle, ‖b y‖ ≤ B)
    (hv : ∀ᵐ y ∂haarAddCircle, y ∉ nodeCell p → v y = 0) (hz : inner ℂ circleOne v = 0) :
    ‖besselHalf Λ ρ hΛ hρ.le (CircleMultiplier.operator b B hb (heat t v))‖^2 ≤
      packetConstant ρ * B^2 * (nodeLength p)^(2*ρ) *
        (min 1 ((nodeLength p)^2/t))^(1-2*ρ) * ‖v‖^2 := by
  let cap : ℝ := min 1 ((nodeLength p)^2/t)
  have hcap : 0 ≤ cap := le_min zero_le_one (by positivity)
  have hl : 0 ≤ nodeLength p := (nodeLength_pos p).le
  have hP : 0 ≤ packetHeatConstant := zero_le_one.trans packetHeatConstant_one_le
  have hu : ‖CircleMultiplier.operator b B hb (heat t v)‖^2 ≤ (B^2*packetHeatConstant*cap)*‖v‖^2 := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) (CircleMultiplier.multiply_norm_le b B hb (heat t v)) 2
    rw [mul_pow] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (supported_mean_zero_heat ht ht1 p v hv hz) (sq_nonneg B)).trans_eq (by
      dsimp only [cap]; ring))
  have hu1 : normOne (CircleMultiplier.operator b B hb (heat t v))^2 ≤ (B^2*nodeLength p)*‖v‖^2 := by
    have hh := (multiply_normOne_le b B hb (heat t v)).trans
      (mul_le_mul_of_nonneg_left ((heat_normOne_le ht v).trans (normOne_supported p v hv)) hB)
    have hs := pow_le_pow_left₀ (normOne_nonneg _) hh 2
    exact hs.trans_eq (by rw [mul_pow,mul_pow,Real.sq_sqrt hl]; ring)
  rw [besselHalf_norm_sq]
  have hh := energy_square_bounds hΛ hρ hρhalf (by positivity : 0 ≤ B^2*packetHeatConstant*cap)
    (mul_nonneg (sq_nonneg B) hl) (sq_nonneg ‖v‖) _ hu hu1
  apply hh.trans_eq
  rw [Real.mul_rpow (mul_nonneg (sq_nonneg B) hP) hcap,
    Real.mul_rpow (sq_nonneg B) hP, Real.mul_rpow (sq_nonneg B) hl]
  calc
    _ = (interpolationConstant ρ*packetHeatConstant^(1-2*ρ)) * (nodeLength p)^(2*ρ) * cap^(1-2*ρ) *
        ((B^2)^(1-2*ρ)*(B^2)^(2*ρ)) * ‖v‖^2 := by ring
    _ = _ := by
      rw [← Real.rpow_add' (sq_nonneg B) (by linarith : 1-2*ρ+2*ρ ≠ 0),
        show 1-2*ρ+2*ρ = 1 by ring, Real.rpow_one]
      unfold packetConstant
      dsimp only [cap]
      ring

end SHE.HaarWeightedHeat
