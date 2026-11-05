module

public import SHE.MixedPastOmittedWord
public import SHE.MixedPastWordMoments
public import SHE.BaselineOriginalGain

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.MixedPastOmittedWord
open Set Real StoppedFourier GaussianAssignmentBlocks
open scoped BigOperators
variable {d r m : ℕ}

theorem restore_factor (P : CanonicalCovariance.ProfileParameters) (lo hi : Fin r→ℝ)
    (age : Fin m→ℝ) (choices : List (Fin r×Fin (m+1))) (j0 : Fin m) (A0 ν : ℝ) :
    factor (d:=d) P lo hi age choices j0 A0 ν*
      NativeAssignedLeafMoments.leafScale P choices j0.succ lo hi (age j0)
        (MinimumGapChoice.blockChoice lo hi choices j0.succ)=
      MixedPastWordMoments.factor (d:=d) P lo hi age choices A0 ν := by
  unfold factor MixedPastWordMoments.factor
  rw [mul_assoc,Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ j0)]

/-- A genuine derivative of the omitted full profile restores its
ORIGINAL empty native-leaf age. This works even when the coefficient
Holder constant is zero; no division by it is used. -/
theorem restored_factor_gain (P : CanonicalCovariance.ProfileParameters) (direction : CircleL2)
    (lo hi : Fin r→ℝ) (age : Fin m→ℝ) (choices : List (Fin r×Fin (m+1)))
    (j0 : Fin m) (hz : block choices j0.succ=[]) (A0 ν : ℝ)
    {gap : ℝ} (hgap : 0<gap) (hga : gap≤age j0) :
    ControlledScoreRates.sharpConstant P direction*(age j0)^((P.exponent-1)/4)*
        |factor (d:=d) P lo hi age choices j0 A0 ν|≤
      BaselineOriginalGain.unitSharp P direction*
        |MixedPastWordMoments.factor (d:=d) P lo hi age choices A0 ν| *gap^(-(1/4:ℝ)) := by
  let s:=NativeAssignedLeafMoments.leafScale P choices j0.succ lo hi (age j0)
    (MinimumGapChoice.blockChoice lo hi choices j0.succ)
  have hs : 0≤s:=by
    simp only [s,NativeAssignedLeafMoments.leafScale,dite_eq_left hz]
    exact mul_nonneg P.holder_nonneg (rpow_nonneg (hgap.le.trans hga) _)
  have hg:=BaselineOriginalGain.empty_leaf_gain P direction choices j0.succ hz lo hi
    (MinimumGapChoice.blockChoice lo hi choices j0.succ) hgap hga
  have hr : |factor (d:=d) P lo hi age choices j0 A0 ν| *s=
      |MixedPastWordMoments.factor (d:=d) P lo hi age choices A0 ν| := by
    rw [←abs_of_nonneg hs,←abs_mul]
    exact congrArg abs (restore_factor P lo hi age choices j0 A0 ν)
  have hh:=mul_le_mul_of_nonneg_right hg (abs_nonneg (factor (d:=d) P lo hi age choices j0 A0 ν))
  rw [←hr]
  convert! hh using 1 <;> ring

/-- Restoring the erased factor in the COMPLETE filtered assignment
total leaves exactly the original full-word time total and a single
fresh quarter-power loss, independently of depth and Holder exponent. -/
theorem restored_total_gain (P : CanonicalCovariance.ProfileParameters) (direction : CircleL2)
    (lo hi : Fin r→ℝ) (age : Fin m→ℝ) (j0 : Fin m) (A0 ν : ℝ)
    {gap : ℝ} (hgap : 0<gap) (hga : gap≤age j0) :
    ControlledScoreRates.sharpConstant P direction*(age j0)^((P.exponent-1)/4)*
        total (d:=d) P lo hi age j0 A0 ν≤
      BaselineOriginalGain.unitSharp P direction*
        MixedPastWordMoments.total (d:=d) P lo hi age A0 ν*gap^(-(1/4:ℝ)) := by
  classical
  let cs:=assignments (m:=m+1) (List.finRange r)
  have hpoint (choices : List (Fin r×Fin (m+1))) (_hc:choices∈cs) :
      ControlledScoreRates.sharpConstant P direction*(age j0)^((P.exponent-1)/4)*
        (if block choices j0.succ=[] then |factor (d:=d) P lo hi age choices j0 A0 ν| else 0)≤
      BaselineOriginalGain.unitSharp P direction*
        |MixedPastWordMoments.factor (d:=d) P lo hi age choices A0 ν| *gap^(-(1/4:ℝ)) := by
    by_cases hz:block choices j0.succ=[]
    · simpa only [ite_eq_left hz] using restored_factor_gain P direction lo hi age choices j0 hz A0 ν hgap hga
    · simp only [ite_eq_right hz,mul_zero]
      exact mul_nonneg (mul_nonneg (BaselineOriginalGain.unitSharp_nonneg P direction) (abs_nonneg _))
        (rpow_nonneg hgap.le _)
  have hs:=List.sum_le_sum hpoint
  simpa only [total,MixedPastWordMoments.total,List.sum_map_mul_left,List.sum_map_mul_right,
    cs,mul_assoc] using hs

end SHE.MixedPastOmittedWord
