module

public import SHE.NativeHeatDilation
public import SHE.HeatKernelAgeComparison

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.HeatMarkov
open Real FourierHeatLine
local instance nativeHeatComparable_unitPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

/-- Comparable-age dilation for the actual normalized periodic Gaussian;
the bound is pointwise and retains the physical spatial parent. -/
theorem kernel_comparable {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (hts : t ≤ 2*s)
    (x : UnitAddCircle) :
    ‖kernel s hs x‖ ≤ sqrt 2*‖kernel t (hs.trans_le hst) x‖ := by
  have hm : heatMass t ≤ sqrt 2*heatMass s :=
    (HeatKernelAgeComparison.mass_mono hts).trans_eq (HeatKernelAgeComparison.mass_scale (by norm_num) hs)
  have hr : heatMass t/heatMass s ≤ sqrt 2 :=
    (div_le_iff₀ (heatMass_pos hs)).mpr hm
  exact (HeatKernelAgeComparison.age_le hs (hs.trans_le hst) hst x).trans
    (mul_le_mul_of_nonneg_right hr (norm_nonneg _))

end SHE.HeatMarkov

namespace SHE.NativeHeatSpan
open Real StoppedFourier
local instance nativeHeatComparable_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩

theorem physical_comparable {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (hts : t ≤ 2*s)
    (a x : HeatCircle) :
    ‖ProfileVariance.heatPhysical s a x‖ ≤ sqrt 2*‖ProfileVariance.heatPhysical t a x‖ := by
  have hden : 0 ≤ 4*π^2 := by positivity
  have hcst : clock s ≤ clock t := div_le_div_of_nonneg_right hst hden
  have hcts : clock t ≤ 2*clock s := by
    have hh := div_le_div_of_nonneg_right hts hden
    simpa only [clock,mul_div_assoc] using hh
  have hh := HeatMarkov.kernel_comparable (clock_pos hs) hcst hcts (unitCenter x-unitCenter a)
  change ‖kernel s hs a x‖ ≤ sqrt 2*‖kernel t (hs.trans_le hst) a x‖ at hh
  simpa only [kernel_eq_physical] using hh

end SHE.NativeHeatSpan
