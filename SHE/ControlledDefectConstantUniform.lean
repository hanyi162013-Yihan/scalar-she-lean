module
public import SHE.ControlledDefectConstants
public import SHE.ControlledSmoothLimit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
namespace SHE.ControlledDefectConstants
open Real
variable {P Q:CanonicalCovariance.ProfileParameters}

/-- The complete bounded-empty packet constant contains only the
numerical Holder exponent of the profile. -/
theorem momentConstant_congr (hβ:P.exponent=Q.exponent)(r m b:ℕ):
    TwoFreshBoundedEmptyWord.momentConstant P r m b=TwoFreshBoundedEmptyWord.momentConstant Q r m b:=by
  unfold TwoFreshBoundedEmptyWord.momentConstant TwoFreshBoundedEmptyMoments.constant
    BoundedEmptyAssignedLeaf.leafConstant
  rw [hβ]

variable (m W:ℝ)(hm:0<m)(hW:0≤W)(ρ:ℝ)(hρ:0<ρ)(hρhalf:ρ<1/2)(k:ℕ)

theorem horizon_congr (h:P.lower=Q.lower):
    horizon P.lower P.lower_pos m W hm hW ρ hρ hρhalf k=
      horizon Q.lower Q.lower_pos m W hm hW ρ hρ hρhalf k:=by
  let f:{r:ℝ//0<r}→ℝ:=fun e=>horizon e.1 e.2 m W hm hW ρ hρ hρhalf k
  have he:(⟨P.lower,P.lower_pos⟩:{r:ℝ//0<r})=⟨Q.lower,Q.lower_pos⟩:=Subtype.ext h
  exact congrArg f he

theorem ageConstant_congr (h:P.lower=Q.lower):
    ageConstant P.lower P.lower_pos m W hm hW ρ hρ hρhalf k=
      ageConstant Q.lower Q.lower_pos m W hm hW ρ hρ hρhalf k:=by
  let f:{r:ℝ//0<r}→ℝ:=fun e=>ageConstant e.1 e.2 m W hm hW ρ hρ hρhalf k
  have he:(⟨P.lower,P.lower_pos⟩:{r:ℝ//0<r})=⟨Q.lower,Q.lower_pos⟩:=Subtype.ext h
  exact congrArg f he

/-- The actual full-mark constant is unchanged by smoothing the
coefficient while preserving the lower floor and Holder exponent. -/
theorem constant_congr (hl:P.lower=Q.lower)(hβ:P.exponent=Q.exponent):
    constant m W hm hW ρ hρ hρhalf k P=constant m W hm hW ρ hρ hρhalf k Q:=by
  unfold constant
  rw [ageConstant_congr m W hm hW ρ hρ hρhalf k hl,momentConstant_congr hβ]

open SmoothApproximation
variable (D:ScalarData){T0:ℝ}(hT0:0<T0)(hT1:T0≤1)
variable (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T0^(D.beta/4)≤1/2)
local notation "Smooth"=>ControlledSmoothLimit.smoothTotalParameters D hT0 hT1 hsmall
local notation "Rough"=>ControlledSmoothLimit.roughTotalParameters D hT0 hT1 hsmall

theorem smooth_horizon (n:ℕ):
    horizon (Smooth n).lower (Smooth n).lower_pos m W hm hW ρ hρ hρhalf k=
      horizon (Rough).lower (Rough).lower_pos m W hm hW ρ hρ hρhalf k:=
  horizon_congr m W hm hW ρ hρ hρhalf k rfl

theorem smooth_constant (n:ℕ):
    constant m W hm hW ρ hρ hρhalf k (Smooth n)=constant m W hm hW ρ hρ hρhalf k Rough:=
  constant_congr m W hm hW ρ hρ hρhalf k rfl rfl
end SHE.ControlledDefectConstants
