module

public import SHE.MixedPastNativeKernelActual
public import SHE.PastMeanTimeIntegral

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace SHE.NativeHigherEnergyFactors
open Real

/-- Both genuine past-profile powers are dominated by the single
integrable past power used by the native higher-row time convolution. -/
theorem past_power {β s:ℝ}(hβ:0≤β)(hs:0<s)(hs1:s≤1):
    (s^((β-1)/4))^2≤s^(-(1/2:ℝ)) := by
  rw [←Real.rpow_mul_natCast hs.le]
  apply Real.rpow_le_rpow_of_exponent_ge hs hs1
  linarith

theorem quarter_power {s:ℝ}(hs:0≤s):
    (s^(-(1/4:ℝ)))^2=s^(-(1/2:ℝ)) := by
  rw [←Real.rpow_mul_natCast hs]
  norm_num

/-- The actual distinguished score amplitude retains exactly the
current L2 displacement in degree chi and the true newest gap. -/
theorem current_factor {C D δ χ:ℝ}(hC:0≤C)(hD:0≤D)(hδ:0<δ):
    (C*(Real.sqrt δ)⁻¹*D)^χ=C^χ*δ^(-χ/2)*D^χ := by
  rw [Real.mul_rpow (mul_nonneg hC (inv_nonneg.mpr (sqrt_nonneg _))) hD,
    Real.mul_rpow hC (inv_nonneg.mpr (sqrt_nonneg _)),Real.inv_rpow (sqrt_nonneg _),sqrt_eq_rpow]
  rw [←Real.rpow_mul hδ.le,←Real.rpow_neg hδ.le]
  congr 2
  ring

/-- The two literal past legs reduce to one structural coefficient.
The original local time s and dependent past displacement D remain. -/
theorem past_factor {ι:Type*}[Fintype ι] (β s D sharp A B:ℝ)(d:ι→ℝ)
    (hβ:0≤β)(hs:0<s)(hs1:s≤1)(hD:0≤D):
    A^2*(sharp/2)^2*((B*s^((β-1)/4))^2*D)+
        (∑j,d j^2)*((s^(-(1/4:ℝ))*sharp)^2*D)≤
      ((A*B/2)^2+∑j,d j^2)*sharp^2*s^(-(1/2:ℝ))*D := by
  have hp:=past_power hβ hs hs1
  have he:=quarter_power hs.le
  rw [mul_pow,mul_pow,he]
  have hmul:=mul_le_mul_of_nonneg_left hp (by positivity : 0≤A^2*(sharp/2)^2*B^2*D)
  nlinarith only [hmul]

end SHE.NativeHigherEnergyFactors
