module

public import SHE.NativeHeatDilation

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.HeatMarkov
open Set MeasureTheory AddCircle FourierHeatLine LineGaussianLocal GaussianPeriodizedLocal
local instance nativeHeatRoot_unitPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

/-- The square root of the actual periodic heat density has a localized
heat envelope at twice the age. Periodization introduces no spatial loss. -/
theorem sqrt_kernel_bound {t : ℝ} (ht : 0 < t) (x : UnitAddCircle) :
    Real.sqrt ‖kernel t ht x‖ ≤
      Real.sqrt 2*Real.sqrt (heatMass t)*‖kernel (2*t) (by positivity) x‖ := by
  induction x using Quotient.inductionOn with
  | _ r =>
    have ht2 : 0 < 2*t := by positivity
    have hs := gaussian_summable ht r
    have hs2 := gaussian_summable ht2 r
    have hn (n : ℤ) : 0 ≤ gaussian (2*t) (r+(n:ℝ)) := (Real.exp_pos _).le
    have hd (n : ℤ) : gaussian t (r+(n:ℝ)) = (gaussian (2*t) (r+(n:ℝ)))^2 := by
      unfold gaussian
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      field_simp
      <;> ring
    have hb (n : ℤ) : gaussian (2*t) (r+(n:ℝ)) ≤ ∑' j : ℤ,gaussian (2*t) (r+(j:ℝ)) := by
      have hh := hs2.sum_le_tsum ({n}:Finset ℤ) (fun j _ => hn j)
      simpa only [Finset.sum_singleton] using hh
    have hh : (∑' n : ℤ,gaussian t (r+(n:ℝ))) ≤
        (∑' n : ℤ,gaussian (2*t) (r+(n:ℝ)))^2 := by
      calc
        _ ≤ ∑' n : ℤ,gaussian (2*t) (r+(n:ℝ))*(∑' j : ℤ,gaussian (2*t) (r+(j:ℝ))) :=
          hs.tsum_le_tsum (fun n => by rw [hd n,pow_two]; exact mul_le_mul_of_nonneg_left (hb n) (hn n))
            (hs2.mul_right _)
        _ = _ := by rw [tsum_mul_right,pow_two]
    have hmass : heatMass (2*t)=Real.sqrt 2*heatMass t := by
      unfold heatMass
      rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      ring
    rw [kernel_coe_norm ht r,kernel_coe_norm ht2 r,hmass]
    have hm := heatMass_pos ht
    have hsum : 0 ≤ ∑' n : ℤ,gaussian (2*t) (r+(n:ℝ)) := tsum_nonneg hn
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · have hh' := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hm.le)
      convert hh' using 1
      field_simp
      nlinarith [Real.sq_sqrt hm.le, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

end SHE.HeatMarkov

namespace SHE.NativeHeatSpan
open Set MeasureTheory AddCircle StoppedFourier HeatPeriodization
local instance nativeHeatRoot_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

def sqrtKernelConstant : ℝ :=
  Real.sqrt 2*(4*Real.pi)^(1/4:ℝ)*(clock 4)^(1/4:ℝ)

theorem sqrtKernelConstant_pos : 0 < sqrtKernelConstant := by
  unfold sqrtKernelConstant
  have : 0 < clock 4 := clock_pos (by norm_num)
  positivity

/-- Exact native-clock square-root comparison. The constant includes the
period-2π normalization and is uniform over every positive age. -/
theorem sqrt_kernel_four_eight {w : ℝ} (hw : 0 < w) (a x : HeatCircle) :
    Real.sqrt ‖ProfileVariance.heatPhysical (4*w) a x‖ ≤
      sqrtKernelConstant*w^(1/4:ℝ)*‖ProfileVariance.heatPhysical (8*w) a x‖ := by
  have hc : clock (4*w)=clock 4*w := by unfold clock; ring
  have hc2 : 2*clock (4*w)=clock (8*w) := by unfold clock; ring
  have hc4 : 0 < clock 4 := clock_pos (by norm_num)
  have hc4w : 0 < clock (4*w) := clock_pos (by positivity)
  have hh := HeatMarkov.sqrt_kernel_bound (clock_pos (by positivity : 0 < 4*w)) (unitCenter x-unitCenter a)
  have he : Real.sqrt (FourierHeatLine.heatMass (clock (4*w))) =
      (4*Real.pi)^(1/4:ℝ)*(clock 4)^(1/4:ℝ)*w^(1/4:ℝ) := by
    unfold FourierHeatLine.heatMass
    rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,← Real.rpow_mul (by positivity : 0 ≤ 4*Real.pi*clock (4*w))]
    norm_num only at *
    rw [hc,Real.mul_rpow (by positivity : 0 ≤ 4*Real.pi) (by positivity : 0 ≤ clock 4*w),
      Real.mul_rpow (clock_pos (by norm_num : (0:ℝ)<4)).le hw.le]
    ring
  rw [he] at hh
  simp only [hc2] at hh
  change Real.sqrt ‖kernel (4*w) (by positivity) a x‖ ≤
    Real.sqrt 2*((4*Real.pi)^(1/4:ℝ)*(clock 4)^(1/4:ℝ)*w^(1/4:ℝ))*‖kernel (8*w) (by positivity) a x‖ at hh
  simpa only [kernel_eq_physical,sqrtKernelConstant,mul_assoc] using hh

end SHE.NativeHeatSpan
