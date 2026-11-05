module
public import SHE.MixedNativeFrozenFactorGammaTime
public import SHE.MixedNativeVarianceGammaTime
public import SHE.NativePairedGammaUniform
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.GammaBandConstants
open Real
open scoped NNReal

/-- The structural gradient constant contains no clock, damping,
frequency, current state or unsmoothed coefficient derivative. -/
def gradient (P:CanonicalCovariance.ProfileParameters) (A ρ:ℝ):ℝ:=
  (2*A*ScalarHeatGradientDifference.constant P.exponent)^2*
    ScalarHeatBandTime.massConstant P.exponent ρ*(ProfileVariance.lowerConstant*P.lower)^(-1-2*ρ)

theorem mass_pos (P:CanonicalCovariance.ProfileParameters) {ρ:ℝ}
    (hρ0:-(1/2:ℝ)<ρ) (hρ1:ρ<1/2):0<ScalarHeatBandTime.massConstant P.exponent ρ:=by
  unfold ScalarHeatBandTime.massConstant
  have h1:0<ρ+1/2:=by linarith
  have h2:0<1-P.exponent/2-ρ:=by linarith [P.exponent_le_one]
  positivity

theorem gradient_nonneg (P:CanonicalCovariance.ProfileParameters) (A:ℝ) {ρ:ℝ}
    (hρ0:-(1/2:ℝ)<ρ) (hρ1:ρ<1/2):0≤gradient P A ρ:=by
  have hc:=mul_pos ProfileVariance.lowerConstant_pos P.lower_pos
  unfold gradient
  have hm:0≤ScalarHeatBandTime.massConstant P.exponent ρ:=(mass_pos P hρ0 hρ1).le
  positivity

theorem variance_nonneg (P:CanonicalCovariance.ProfileParameters) (A:ℝ) {ρ:ℝ}
    (hρ0:-(1/2:ℝ)<ρ) (hρ1:ρ<1/2):0≤MixedNativeVarianceGammaTime.constant P A ρ:=by
  have hc:=mul_pos ProfileVariance.lowerConstant_pos P.lower_pos
  unfold MixedNativeVarianceGammaTime.constant
  have hp:0<(P.exponent-1)/2+1:=by linarith [P.exponent_pos]
  have h1:0<ρ+3/2:=by linarith
  have h2:0<1-P.exponent/2-ρ:=by linarith [P.exponent_le_one]
  positivity

theorem frozen_factor_nonneg (P:CanonicalCovariance.ProfileParameters) (A:ℝ) {ρ:ℝ}
    (hρ0:-(1/2:ℝ)<ρ) (hρ1:ρ<1/2):0≤MixedNativeFrozenFactorGammaTime.constant P A ρ:=by
  have hc:=mul_pos ProfileVariance.lowerConstant_pos P.lower_pos
  unfold MixedNativeFrozenFactorGammaTime.constant
  have hp:0<(P.exponent-1)/2+1:=by linarith [P.exponent_pos]
  have h1:0<ρ+1/2:=by linarith
  have h2:0<1-P.exponent/2-ρ:=by linarith [P.exponent_le_one]
  positivity

theorem higher_nonneg (m W:ℝ) (hm:0<m) {ρ:ℝ} (hρ:0<ρ) (hρ1:ρ<1/2):
    0≤HaarWeightedHeat.higherConstant m W hm 0 ρ:=by
  unfold HaarWeightedHeat.higherConstant
  have hp:=HaarWeightedHeat.packetConstant_nonneg hρ1
  have hd:0≤DyadicPowerSeries.constant (1-2*ρ) (2-4*ρ):=
    (DyadicPowerSeries.constant_pos (by linarith:0<1-2*ρ) (by linarith:1-2*ρ<2-4*ρ)).le
  positivity

theorem reference_clip_nonneg (P:CanonicalCovariance.ProfileParameters) {κ:ℝ} (hκ:κ<P.lower) (B:ℝ≥0):
    0≤2*((0-1:ℝ)^2+(B:ℝ)*PastReferenceBracket.energyConstant P κ 0 1 1):=by
  have hc:=PastReferenceBracket.energyConstant_nonneg P hκ (show 0≤(1:ℝ) by norm_num) 0 1
  positivity
end SHE.GammaBandConstants
