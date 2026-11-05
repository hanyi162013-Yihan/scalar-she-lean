module
public import SHE.ControlledDefectAgeRMS
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
namespace SHE.ControlledDefectConstants
open Real OrderedHeatForests
variable (ellP:ℝ)(hellP:0<ellP)(m W:ℝ)(hm:0<m)(hW:0≤W)
variable (ρ:ℝ)(hρ:0<ρ)(hρhalf:ρ<1/2)(k:ℕ)
def horizon:ℝ:=Classical.choose (ControlledDefectAgeRMS.rms ellP hellP hm hW hρ hρhalf k)
def ageConstant:ℝ:=Classical.choose (Classical.choose_spec
  (ControlledDefectAgeRMS.rms ellP hellP hm hW hρ hρhalf k))
theorem horizon_pos:0<horizon ellP hellP m W hm hW ρ hρ hρhalf k:=
  (Classical.choose_spec (Classical.choose_spec (ControlledDefectAgeRMS.rms ellP hellP hm hW hρ hρhalf k))).1
theorem ageConstant_pos:0<ageConstant ellP hellP m W hm hW ρ hρ hρhalf k:=
  (Classical.choose_spec (Classical.choose_spec (ControlledDefectAgeRMS.rms ellP hellP hm hW hρ hρhalf k))).2.1

def constant (P:CanonicalCovariance.ProfileParameters):ℝ:=
  1+ageConstant P.lower P.lower_pos m W hm hW ρ hρ hρhalf k*
    sqrt (TwoFreshBoundedEmptyWord.momentConstant P k k 1)*
      (Fintype.card (Choices 1 k):ℝ)

theorem constant_pos (P:CanonicalCovariance.ProfileParameters):
    0<constant m W hm hW ρ hρ hρhalf k P:=by
  have hc:0<ageConstant P.lower P.lower_pos m W hm hW ρ hρ hρhalf k:=
    ageConstant_pos P.lower P.lower_pos m W hm hW ρ hρ hρhalf k
  unfold constant
  positivity
end SHE.ControlledDefectConstants
