module
public import SHE.JointGammaConstantUniform
public import SHE.MixedNativeGammaEnergy
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SHE.JointGammaConstants
open scoped NNReal

/-- The structural constant with the ACTUAL common ellipticity window
used by the constructed mixed pair. -/
def nativeConstant (P:CanonicalCovariance.ProfileParameters) (A κ ell M:ℝ)
    (hell:0<ell) (hκP:κ<P.lower) {ρ:ℝ} (hρ:0<ρ) (hρhalf:ρ<1/2) (Bnext:ℝ≥0):ℝ:=
  constant P A κ (MixedNativeGammaEnergy.commonLower (ell:=ell) (P:=P) (κ:=κ))
    (MixedNativeGammaEnergy.commonUpper (M:=M) (P:=P) (κ:=κ))
    (MixedNativeGammaEnergy.commonLower_pos (ell:=ell) (P:=P) (κ:=κ) (hell:=hell) (hκP:=hκP))
    hρ hρhalf Bnext

/-- The actual min/max common coefficient window also depends only on
uniform structural data. This includes its proof-dependent positive
lower-bound argument. -/
theorem native_constant_congr (P Q:CanonicalCovariance.ProfileParameters)
    (hl:P.lower=Q.lower)(hu:P.upper=Q.upper)(hH:P.holder=Q.holder)(hβ:P.exponent=Q.exponent)
    (A κ ell M:ℝ)(hell:0<ell)(hκP:κ<P.lower)(hκQ:κ<Q.lower)
    {ρ:ℝ}(hρ:0<ρ)(hρhalf:ρ<1/2)(Bnext:ℝ≥0):
    nativeConstant P A κ ell M hell hκP hρ hρhalf Bnext=
      nativeConstant Q A κ ell M hell hκQ hρ hρhalf Bnext:=by
  unfold nativeConstant
  dsimp only [MixedNativeGammaEnergy.commonLower,MixedNativeGammaEnergy.commonUpper]
  simp only [←hl,←hu]
  exact constant_congr P Q hl hu hH hβ A κ (min ell (P.lower-κ))
    (max M (P.upper-κ)) (lt_min hell (sub_pos.mpr hκP)) hρ hρhalf Bnext

/-- ONE complete actual-pair Gamma constant for every canonical smooth
companion index, including the profile-dependent common ellipticity
window. No derivative bound or approximation index enters this value. -/
theorem smooth_native_constant (D:SmoothApproximation.ScalarData){h:ℝ}(hh:0<h)(hh1:h≤1)
    (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*h^(D.beta/4)≤1/2)
    (A κ ell M:ℝ)(hell:0<ell){ρ:ℝ}(hρ:0<ρ)(hρhalf:ρ<1/2)(Bnext:ℝ≥0)(n k:ℕ)
    (hκn:κ<(ControlledSmoothLimit.smoothTotalParameters D hh hh1 hsmall n).lower)
    (hκk:κ<(ControlledSmoothLimit.smoothTotalParameters D hh hh1 hsmall k).lower):
    nativeConstant (ControlledSmoothLimit.smoothTotalParameters D hh hh1 hsmall n)
      A κ ell M hell hκn hρ hρhalf Bnext=
    nativeConstant (ControlledSmoothLimit.smoothTotalParameters D hh hh1 hsmall k)
      A κ ell M hell hκk hρ hρhalf Bnext:=by
  apply native_constant_congr <;> rfl
end SHE.JointGammaConstants
