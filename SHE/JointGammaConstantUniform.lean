module
public import SHE.JointGammaConstants
public import SHE.ControlledSmoothLimit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SHE.JointGammaConstants
open scoped NNReal

/-- The complete Gamma constant depends only on the four displayed
uniform profile parameters, never on the coefficient or its derivatives. -/
theorem constant_congr (P Q:CanonicalCovariance.ProfileParameters)
    (hl:P.lower=Q.lower)(hu:P.upper=Q.upper)(hH:P.holder=Q.holder)(hβ:P.exponent=Q.exponent)
    (A κ m W:ℝ)(hm:0<m){ρ:ℝ}(hρ:0<ρ)(hρhalf:ρ<1/2)(Bnext:ℝ≥0):
    constant P A κ m W hm hρ hρhalf Bnext=constant Q A κ m W hm hρ hρhalf Bnext:=by
  dsimp only [constant,signed,linear,clipped,rootClip,GammaBandConstants.gradient,
    MixedNativeFrozenFactorPositive.constant,MixedNativeVarianceGammaTime.constant,
    ControlledScalarCovarianceTail.constant,PastReferenceBracket.energyConstant]
  simp only [hl,hu,hH,hβ]

/-- The actual smooth companion approximations have ONE complete-Gamma
constant. The approximation index affects only the coefficient itself. -/
theorem smooth_constant (D:SmoothApproximation.ScalarData){h:ℝ}(hh:0<h)(hh1:h≤1)
    (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*h^(D.beta/4)≤1/2)
    (A κ m W:ℝ)(hm:0<m){ρ:ℝ}(hρ:0<ρ)(hρhalf:ρ<1/2)(Bnext:ℝ≥0)(n k:ℕ):
    constant (ControlledSmoothLimit.smoothTotalParameters D hh hh1 hsmall n) A κ m W hm hρ hρhalf Bnext=
      constant (ControlledSmoothLimit.smoothTotalParameters D hh hh1 hsmall k) A κ m W hm hρ hρhalf Bnext:=by
  apply constant_congr <;> rfl
end SHE.JointGammaConstants
