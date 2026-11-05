module

public import SHE.ControlledScoreRates
public import SHE.NativeAssignedLeafMoments

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.BaselineOriginalGain
open Real ProfileStability ControlledScoreRates StoppedFourier GaussianAssignmentBlocks

/-- The coefficient Holder factor is left explicit, including the
constant-coefficient case where it is zero. -/
def unitSharp (P : CanonicalCovariance.ProfileParameters) (d : CircleL2) : ℝ :=
  2*(GaussianAudit.gaussianAbsMoment (P.exponent+1)*
    (ProfileVariance.lowerConstant*P.lower)^((P.exponent-1)/2)*‖d‖)

theorem unitSharp_nonneg (P : CanonicalCovariance.ProfileParameters) (d : CircleL2) :
    0≤unitSharp P d := by
  unfold unitSharp
  exact mul_nonneg (by norm_num) (mul_nonneg
    (mul_nonneg (GaussianAudit.gaussianAbsMoment_nonneg (P.exponent+1))
      (rpow_nonneg (mul_nonneg ProfileVariance.lowerConstant_pos.le P.lower_pos.le) _)) (norm_nonneg _))

theorem sharpConstant_eq (P : CanonicalCovariance.ProfileParameters) (d : CircleL2) :
    sharpConstant P d=P.holder*unitSharp P d := by
  unfold sharpConstant unitSharp meanConstant
  ring

/-- An omitted unassigned baseline leaf recovers its ORIGINAL full age
gain. Only a fresh quarter-power singularity remains, independent of the
number of leaves; no division by the Holder constant occurs. -/
theorem original_age_gain (P : CanonicalCovariance.ProfileParameters) (d : CircleL2)
    {gap age : ℝ} (hgap : 0<gap) (hga : gap≤age) :
    sharpConstant P d*age^((P.exponent-1)/4)≤
      unitSharp P d*(P.holder*age^(P.exponent/4))*gap^(-(1/4:ℝ)) := by
  have ha : 0<age := hgap.trans_le hga
  have hp := Real.rpow_le_rpow_of_nonpos hgap hga (by norm_num : -(1/4:ℝ)≤0)
  have he : age^((P.exponent-1)/4)=age^(P.exponent/4)*age^(-(1/4:ℝ)) := by
    rw [←Real.rpow_add ha]
    congr 1
    ring
  rw [sharpConstant_eq,he]
  have hpos : 0≤unitSharp P d*(P.holder*age^(P.exponent/4)) :=
    mul_nonneg (unitSharp_nonneg P d) (mul_nonneg P.holder_nonneg (rpow_nonneg ha.le _))
  convert! mul_le_mul_of_nonneg_left hp hpos using 1
  ring

theorem empty_leaf_gain {r k : ℕ} (P : CanonicalCovariance.ProfileParameters) (d : CircleL2)
    (choices : List (Fin r×Fin k)) (factor : Fin k) (hblock : block choices factor=[])
    (lo hi : Fin r→ℝ) (chosen : block choices factor≠[]→Fin r)
    {gap age : ℝ} (hgap : 0<gap) (hga : gap≤age) :
    sharpConstant P d*age^((P.exponent-1)/4)≤unitSharp P d*
      NativeAssignedLeafMoments.leafScale P choices factor lo hi age chosen*gap^(-(1/4:ℝ)) := by
  simpa only [NativeAssignedLeafMoments.leafScale,dite_eq_left hblock] using original_age_gain P d hgap hga

end SHE.BaselineOriginalGain
