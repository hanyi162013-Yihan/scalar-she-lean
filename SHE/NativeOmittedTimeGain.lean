module
public import SHE.NativeOmittedTimeTotal
public import SHE.BaselineUnitGain
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.NativeOmittedTimeTotal
open Set Real GaussianAssignmentBlocks StoppedFourier
open scoped BigOperators
variable {d r m:ℕ}

/-- The omitted baseline retains its ORIGINAL leaf age and all original
assignment gains. The remaining quarter-power is the PAST age q,
not the remaining fresh gap. No Holder constant is divided out. -/
theorem restored_total_unit_gain (P:CanonicalCovariance.ProfileParameters)
    (lo hi:Fin r→ℝ) (age:Fin m→ℝ) (j0:Fin m) (A0 ν:ℝ)
    {q:ℝ} (hq:0<q) (ha:q≤age j0):
    ControlledProfile.sharpUnit P*(age j0)^((P.exponent-1)/4)*
      total (d:=d) P lo hi age j0 A0 ν≤
      BaselineOriginalGain.unitCoefficient P*q^(-(1/4:ℝ))*
        MixedPastWordMoments.total (d:=d) P lo hi age A0 ν:=by
  unfold total MixedPastWordMoments.total
  rw [←List.sum_map_mul_left,←List.sum_map_mul_left]
  apply List.sum_le_sum
  intro cs hc
  by_cases hb:block cs j0.succ=[]
  · let s:=NativeAssignedLeafMoments.leafScale P cs j0.succ lo hi (age j0)
      (MinimumGapChoice.blockChoice lo hi cs j0.succ)
    have hs:0≤s:=by
      simp only [s,NativeAssignedLeafMoments.leafScale,dite_eq_left hb]
      exact mul_nonneg P.holder_nonneg (rpow_nonneg (hq.le.trans ha) _)
    have hg:=BaselineOriginalGain.empty_leaf_unit_gain P cs j0.succ hb lo hi
      (MinimumGapChoice.blockChoice lo hi cs j0.succ) hq ha
    have hr:|factor (d:=d) P lo hi age cs j0 A0 ν| * s=
        |MixedPastWordMoments.factor (d:=d) P lo hi age cs A0 ν|:=by
      rw [←abs_of_nonneg hs,←abs_mul]
      exact congrArg abs (restore_factor P lo hi age cs j0 A0 ν hb)
    have hh:=mul_le_mul_of_nonneg_right hg (abs_nonneg (factor (d:=d) P lo hi age cs j0 A0 ν))
    rw [←hr]
    convert! hh using 1 <;> ring
  · simp only [factor,hb,ite_false,abs_zero,mul_zero]
    exact mul_nonneg (mul_nonneg (BaselineOriginalGain.unitCoefficient_nonneg P) (rpow_nonneg hq.le _))
      (abs_nonneg _)


end SHE.NativeOmittedTimeTotal
