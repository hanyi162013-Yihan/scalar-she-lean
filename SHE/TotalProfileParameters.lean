module

public import SHE.AdditiveProfile

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.TotalProfileParameters
open MeasureTheory GaussianProfile ProfileVariance CanonicalCovariance AdditiveProfile

theorem contractionConstant_antitone_lower {ell ell' H β : ℝ} (hell : 0 < ell)
    (horder : ell ≤ ell') (hH : 0 ≤ H) (hβ : β ≤ 2) :
    contractionConstant ell' H β ≤ contractionConstant ell H β := by
  unfold contractionConstant
  apply mul_le_mul_of_nonneg_left
  · exact Real.rpow_le_rpow_of_nonpos (mul_pos lowerConstant_pos hell)
      (mul_le_mul_of_nonneg_left horder lowerConstant_pos.le) (by linarith)
  · exact mul_nonneg upperConstant_pos.le
      (mul_nonneg (div_nonneg hH (by norm_num)) (incrementMoment_nonneg β))

/-- Add the common independent variance to both the coefficient and its
reference profile. The old horizon remains valid because the Gaussian
variance contraction improves as the elliptic lower bound increases. -/
def add (P : ProfileParameters) (m : ℝ) : ProfileParameters where
  coefficient := totalCoefficient m P.coefficient
  lower := m^2+P.lower
  upper := m^2+P.upper
  holder := P.holder
  exponent := P.exponent
  horizon := P.horizon
  measurable := measurable_const.add P.measurable
  lower_pos := add_pos_of_nonneg_of_pos (sq_nonneg _) P.lower_pos
  upper_nonneg := add_nonneg (sq_nonneg _) P.upper_nonneg
  holder_nonneg := P.holder_nonneg
  exponent_pos := P.exponent_pos
  exponent_le_one := P.exponent_le_one
  horizon_pos := P.horizon_pos
  horizon_le_one := P.horizon_le_one
  lower_bound := fun z => add_le_add le_rfl (P.lower_bound z)
  upper_bound := fun z => add_le_add le_rfl (P.upper_bound z)
  holder_bound := fun z w => by
    simpa only [totalCoefficient,add_sub_add_left_eq_sub] using P.holder_bound z w
  small := (mul_le_mul_of_nonneg_right
    (contractionConstant_antitone_lower P.lower_pos (le_add_of_nonneg_left (sq_nonneg m))
      P.holder_nonneg (P.exponent_le_one.trans (by norm_num)))
    (Real.rpow_nonneg P.horizon_pos.le _)).trans P.small

theorem add_lower (P : ProfileParameters) (m : ℝ) : (add P m).lower=m^2+P.lower := rfl
theorem add_coefficient (P : ProfileParameters) (m z : ℝ) :
    (add P m).coefficient z=m^2+P.coefficient z := rfl
theorem add_horizon (P : ProfileParameters) (m : ℝ) : (add P m).horizon=P.horizon := rfl

end SHE.TotalProfileParameters
