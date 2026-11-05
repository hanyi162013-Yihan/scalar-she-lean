module

public import SHE.OmittedRestoreTotal
public import SHE.RandomProfileEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.BaselineOriginalGain
open Real ProfileStability ControlledScoreRates StoppedFourier GaussianAssignmentBlocks

/-- The actual random derivative RMS coefficient with its Holder factor
left explicit. In particular no division by a possibly zero Holder
constant is needed to restore an erased native leaf. -/
def unitCoefficient (P : CanonicalCovariance.ProfileParameters) : ℝ :=
  2*(GaussianAudit.gaussianAbsMoment (P.exponent+1)*
    (ProfileVariance.lowerConstant*P.lower)^((P.exponent-1)/2))

theorem unitCoefficient_nonneg (P : CanonicalCovariance.ProfileParameters) :
    0≤unitCoefficient P := by
  unfold unitCoefficient
  exact mul_nonneg (by norm_num) (mul_nonneg
    (GaussianAudit.gaussianAbsMoment_nonneg (P.exponent+1))
    (rpow_nonneg (mul_nonneg ProfileVariance.lowerConstant_pos.le P.lower_pos.le) _))

theorem sharpUnit_eq (P : CanonicalCovariance.ProfileParameters) :
    ControlledProfile.sharpUnit P=P.holder*unitCoefficient P := by
  unfold ControlledProfile.sharpUnit unitCoefficient meanConstant
  ring

theorem original_age_unit_gain (P : CanonicalCovariance.ProfileParameters)
    {gap age : ℝ} (hgap : 0<gap) (hga : gap≤age) :
    ControlledProfile.sharpUnit P*age^((P.exponent-1)/4)≤
      unitCoefficient P*(P.holder*age^(P.exponent/4))*gap^(-(1/4:ℝ)) := by
  have ha : 0<age := hgap.trans_le hga
  have hp := Real.rpow_le_rpow_of_nonpos hgap hga (by norm_num : -(1/4:ℝ)≤0)
  have he : age^((P.exponent-1)/4)=age^(P.exponent/4)*age^(-(1/4:ℝ)) := by
    rw [←Real.rpow_add ha]
    congr 1
    ring
  rw [sharpUnit_eq,he]
  have hpos : 0≤unitCoefficient P*(P.holder*age^(P.exponent/4)) :=
    mul_nonneg (unitCoefficient_nonneg P) (mul_nonneg P.holder_nonneg (rpow_nonneg ha.le _))
  convert! mul_le_mul_of_nonneg_left hp hpos using 1
  ring

theorem empty_leaf_unit_gain {r k : ℕ} (P : CanonicalCovariance.ProfileParameters)
    (choices : List (Fin r×Fin k)) (factor : Fin k) (hblock : block choices factor=[])
    (lo hi : Fin r→ℝ) (chosen : block choices factor≠[]→Fin r)
    {gap age : ℝ} (hgap : 0<gap) (hga : gap≤age) :
    ControlledProfile.sharpUnit P*age^((P.exponent-1)/4)≤unitCoefficient P*
      NativeAssignedLeafMoments.leafScale P choices factor lo hi age chosen*gap^(-(1/4:ℝ)) := by
  simpa only [NativeAssignedLeafMoments.leafScale,dite_eq_left hblock] using original_age_unit_gain P hgap hga

end SHE.BaselineOriginalGain

namespace SHE.MixedPastOmittedWord
open Set Real StoppedFourier GaussianAssignmentBlocks
open scoped BigOperators
variable {d r m : ℕ}
theorem restored_factor_unit_gain (P : CanonicalCovariance.ProfileParameters)
    (lo hi : Fin r→ℝ) (age : Fin m→ℝ) (choices : List (Fin r×Fin (m+1)))
    (j0 : Fin m) (hz : block choices j0.succ=[]) (A0 ν : ℝ)
    {gap : ℝ} (hgap : 0<gap) (hga : gap≤age j0) :
    ControlledProfile.sharpUnit P*(age j0)^((P.exponent-1)/4)*
        |factor (d:=d) P lo hi age choices j0 A0 ν|≤
      BaselineOriginalGain.unitCoefficient P*
        |MixedPastWordMoments.factor (d:=d) P lo hi age choices A0 ν| *gap^(-(1/4:ℝ)) := by
  let s:=NativeAssignedLeafMoments.leafScale P choices j0.succ lo hi (age j0)
    (MinimumGapChoice.blockChoice lo hi choices j0.succ)
  have hs : 0≤s:=by
    simp only [s,NativeAssignedLeafMoments.leafScale,dite_eq_left hz]
    exact mul_nonneg P.holder_nonneg (rpow_nonneg (hgap.le.trans hga) _)
  have hg:=BaselineOriginalGain.empty_leaf_unit_gain P choices j0.succ hz lo hi
    (MinimumGapChoice.blockChoice lo hi choices j0.succ) hgap hga
  have hr : |factor (d:=d) P lo hi age choices j0 A0 ν| *s=
      |MixedPastWordMoments.factor (d:=d) P lo hi age choices A0 ν| := by
    rw [←abs_of_nonneg hs,←abs_mul]
    exact congrArg abs (restore_factor P lo hi age choices j0 A0 ν)
  have hh:=mul_le_mul_of_nonneg_right hg (abs_nonneg (factor (d:=d) P lo hi age choices j0 A0 ν))
  rw [←hr]
  convert! hh using 1
  ring

/-- Restoring the erased factor in the COMPLETE filtered assignment
total leaves exactly the original full-word time total and a single
fresh quarter-power loss, independently of depth and Holder exponent. -/
theorem restored_total_unit_gain (P : CanonicalCovariance.ProfileParameters)
    (lo hi : Fin r→ℝ) (age : Fin m→ℝ) (j0 : Fin m) (A0 ν : ℝ)
    {gap : ℝ} (hgap : 0<gap) (hga : gap≤age j0) :
    ControlledProfile.sharpUnit P*(age j0)^((P.exponent-1)/4)*
        total (d:=d) P lo hi age j0 A0 ν≤
      BaselineOriginalGain.unitCoefficient P*
        MixedPastWordMoments.total (d:=d) P lo hi age A0 ν*gap^(-(1/4:ℝ)) := by
  classical
  let cs:=assignments (m:=m+1) (List.finRange r)
  have hpoint (choices : List (Fin r×Fin (m+1))) (_hc:choices∈cs) :
      ControlledProfile.sharpUnit P*(age j0)^((P.exponent-1)/4)*
        (if block choices j0.succ=[] then |factor (d:=d) P lo hi age choices j0 A0 ν| else 0)≤
      BaselineOriginalGain.unitCoefficient P*
        |MixedPastWordMoments.factor (d:=d) P lo hi age choices A0 ν| *gap^(-(1/4:ℝ)) := by
    by_cases hz:block choices j0.succ=[]
    · simpa only [ite_eq_left hz] using restored_factor_unit_gain P lo hi age choices j0 hz A0 ν hgap hga
    · simp only [ite_eq_right hz,mul_zero]
      exact mul_nonneg (mul_nonneg (BaselineOriginalGain.unitCoefficient_nonneg P) (abs_nonneg _))
        (rpow_nonneg hgap.le _)
  have hs:=List.sum_le_sum hpoint
  simpa only [total,MixedPastWordMoments.total,List.sum_map_mul_left,List.sum_map_mul_right,
    cs,mul_assoc] using hs


end SHE.MixedPastOmittedWord
