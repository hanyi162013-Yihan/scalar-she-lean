module

public import SHE.CircleModulus

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.HeatL1L2
open MeasureTheory AddCircle CircleHeat HeatMarkov FiniteHaar
local instance : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

def constant : ℝ := 1+2*HeatTrace.fractionalGaussianIntegral 0

theorem constant_pos : 0 < constant := by
  have hg := (HeatTrace.fractionalGaussianIntegral_pos (by norm_num : (0:ℝ) < 1/2)).le
  unfold constant
  linarith

/-- Actual heat L¹-to-L² smoothing from the complete Fourier series and
the literal normalized periodic heat trace. -/
theorem norm_sq_bound {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (f : CircleL2) :
    ‖heat t f‖^2 ≤ constant*t^(-(1/2:ℝ))*normOne f^2 := by
  have hb (n : ℤ) : ‖fourierCoeff (heat t f) n‖^2 ≤ ‖heatWeight t n‖^2*normOne f^2 := by
    rw [heat_fourierCoeff,norm_mul,mul_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (fourierCoeff_norm_le_normOne f n) 2) (sq_nonneg _)
  have hs := (summable_fourier_sq (heat t f)).tsum_le_tsum hb
    ((heatWeight_square_summable ht).mul_right (normOne f^2))
  rw [← norm_sq_fourier,tsum_mul_right] at hs
  have hc := heatWeight_trace_bound ht
  have htneg : 1 ≤ t^(-(1/2:ℝ)) := by
    simpa using Real.rpow_le_rpow_of_nonpos ht ht1 (by norm_num : -(1/2:ℝ) ≤ 0)
  have htrace : (∑' n : ℤ,‖heatWeight t n‖^2) ≤ constant*t^(-(1/2:ℝ)) := by
    unfold constant
    nlinarith only [hc,htneg]
  exact hs.trans (mul_le_mul_of_nonneg_right htrace (sq_nonneg _))

end SHE.HeatL1L2
