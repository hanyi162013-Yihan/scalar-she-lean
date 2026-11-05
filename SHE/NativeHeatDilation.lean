module

public import SHE.NativeHeatConvolution
public import SHE.GaussianPeriodizedLocal

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.HeatMarkov
open Set MeasureTheory AddCircle FourierHeatLine LineGaussianLocal GaussianPeriodizedLocal
local instance nativeHeatDilation_unitPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

/-- Genuine dilation comparison for the actual normalized periodic heat
kernel. Its factor is the exact one-dimensional Gaussian mass ratio. -/
theorem kernel_double_bound {t : ℝ} (ht : 0 < t) (x : UnitAddCircle) :
    ‖kernel t ht x‖ ≤ Real.sqrt 2*‖kernel (2*t) (by positivity) x‖ := by
  induction x using Quotient.inductionOn with
  | _ r =>
    have hg (n : ℤ) : gaussian t (r+(n:ℝ)) ≤ gaussian (2*t) (r+(n:ℝ)) := by
      apply Real.exp_le_exp.mpr
      apply (div_le_div_iff₀ (by positivity : 0 < 4*t) (by positivity : 0 < 4*(2*t))).mpr
      nlinarith [sq_nonneg (r+(n:ℝ))]
    have hs := (gaussian_summable ht r).tsum_le_tsum hg (gaussian_summable (by positivity : 0 < 2*t) r)
    have hm : heatMass (2*t)=Real.sqrt 2*heatMass t := by
      unfold heatMass
      rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      ring
    rw [kernel_coe_norm ht r,kernel_coe_norm (by positivity : 0 < 2*t) r,hm]
    calc
      _ ≤ (heatMass t)⁻¹*(∑' n : ℤ,gaussian (2*t) (r+(n:ℝ))) :=
        mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (heatMass_pos ht).le)
      _ = _ := by field_simp

end SHE.HeatMarkov

namespace SHE.NativeHeatSpan
open Set MeasureTheory AddCircle StoppedFourier
local instance nativeHeatDilation_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

theorem kernel_double_bound {t : ℝ} (ht : 0 < t) (a x : HeatCircle) :
    ‖kernel t ht a x‖ ≤ Real.sqrt 2*‖kernel (2*t) (by positivity) a x‖ := by
  have hc : clock (2*t)=2*clock t := by unfold clock; ring
  change ‖HeatMarkov.kernel (clock t) _ (unitCenter x-unitCenter a)‖ ≤
    Real.sqrt 2*‖HeatMarkov.kernel (clock (2*t)) _ (unitCenter x-unitCenter a)‖
  simpa only [hc] using HeatMarkov.kernel_double_bound (clock_pos ht) (unitCenter x-unitCenter a)

theorem physical_double_bound {t : ℝ} (ht : 0 < t) (a x : HeatCircle) :
    ‖ProfileVariance.heatPhysical t a x‖ ≤ Real.sqrt 2*‖ProfileVariance.heatPhysical (2*t) a x‖ := by
  simpa only [kernel_eq_physical] using kernel_double_bound ht a x

/-- Every actual old second-score heat edge at age `2a` is dominated
by the common terminal first-score edge at age `4a`. -/
theorem physical_two_le_four {t : ℝ} (ht : 0 < t) (a x : HeatCircle) :
    ‖ProfileVariance.heatPhysical (2*t) a x‖ ≤ Real.sqrt 2*‖ProfileVariance.heatPhysical (4*t) a x‖ := by
  simpa only [show 2*(2*t)=4*t by ring] using physical_double_bound (by positivity : 0 < 2*t) a x

end SHE.NativeHeatSpan
