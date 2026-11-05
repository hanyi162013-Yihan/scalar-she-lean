module
public import SHE.GammaBandConstants
public import SHE.NativeConvexGammaUniform
public import SHE.GammaClipCollapse
public import SHE.MixedNativeFrozenFactorPositive
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SHE.JointGammaConstants
open Real
open scoped NNReal ENNReal

/-- Structural signed-input coefficient with the exact native clock. -/
def signed (P:CanonicalCovariance.ProfileParameters)(A:ℝ):ℝ:=
  (4*π^2)^(1/2:ℝ)*(A*ScalarHeatBandEnvelope.constant P.exponent 0)^2*
    ScalarHeatBandTime.massConstant P.exponent 0*(ProfileVariance.lowerConstant*P.lower)⁻¹

def weight (κ W ρ:ℝ):ℝ:=(κ+W)*(1+2*HeatTrace.fractionalGaussianIntegral ρ)
def rootClip (P:CanonicalCovariance.ProfileParameters)(κ:ℝ)(Bnext:ℝ≥0):ℝ:=
  2*((0-1:ℝ)^2+(Bnext:ℝ)*PastReferenceBracket.energyConstant P κ 0 1 1)
def linear (P:CanonicalCovariance.ProfileParameters)(A κ m W:ℝ)(hm:0<m)(ρ:ℝ):ℝ:=
  HaarWeightedHeat.higherConstant m W hm 0 ρ*MixedNativeFrozenFactorPositive.constant P A ρ+
    2*weight κ W ρ*MixedNativeVarianceGammaTime.constant P A ρ
def clipped (P:CanonicalCovariance.ProfileParameters)(A κ W ρ:ℝ):ℝ:=
  weight κ W ρ*GammaBandConstants.gradient P A ρ

/-- Chosen independently of damping, every time, band, sample and
smooth coefficient derivative; only the uniform structural data occur. -/
def constant (P:CanonicalCovariance.ProfileParameters)(A κ m W:ℝ)(hm:0<m)
    {ρ:ℝ}(hρ:0<ρ)(hρhalf:ρ<1/2)(Bnext:ℝ≥0):ℝ:=
  1+6*(NativeConvexGammaUniform.constant m W hm hρ hρhalf*signed P A+linear P A κ m W hm ρ+
    clipped P A κ W ρ*(max 1 (4:ℝ)+max 1 (rootClip P κ Bnext)))

theorem signed_nonneg (P:CanonicalCovariance.ProfileParameters)(A:ℝ):0≤signed P A:=by
  have hc:=mul_pos ProfileVariance.lowerConstant_pos P.lower_pos
  have hb:0≤ScalarHeatBandTime.massConstant P.exponent 0:=
    (GammaBandConstants.mass_pos P (by norm_num) (by norm_num)).le
  unfold signed
  positivity

theorem weight_nonneg {κ W ρ:ℝ}(hκ:0≤κ)(hW:0≤W)(hρhalf:ρ<1/2):0≤weight κ W ρ:=by
  unfold weight
  exact mul_nonneg (add_nonneg hκ hW) (by linarith [HeatTrace.fractionalGaussianIntegral_pos hρhalf])

theorem linear_nonneg (P:CanonicalCovariance.ProfileParameters)(A κ m W:ℝ)(hm:0<m)
    {ρ:ℝ}(hκ:0≤κ)(hW:0≤W)(hρ:0<ρ)(hρhalf:ρ<1/2):0≤linear P A κ m W hm ρ:=by
  have hρ0:-(1/2:ℝ)<ρ:=by linarith
  have hh:=GammaBandConstants.higher_nonneg m W hm hρ hρhalf
  have hf:=GammaBandConstants.frozen_factor_nonneg P A hρ0 hρhalf
  have hv:=GammaBandConstants.variance_nonneg P A hρ0 hρhalf
  have hw:=weight_nonneg hκ hW hρhalf
  change 0≤HaarWeightedHeat.higherConstant m W hm 0 ρ*MixedNativeFrozenFactorGammaTime.constant P A ρ+
    2*weight κ W ρ*MixedNativeVarianceGammaTime.constant P A ρ
  positivity

theorem clipped_nonneg (P:CanonicalCovariance.ProfileParameters)(A κ W:ℝ){ρ:ℝ}
    (hκ:0≤κ)(hW:0≤W)(hρ:0<ρ)(hρhalf:ρ<1/2):0≤clipped P A κ W ρ:=
  mul_nonneg (weight_nonneg hκ hW hρhalf)
    (GammaBandConstants.gradient_nonneg P A (by linarith) hρhalf)

theorem constant_pos (P:CanonicalCovariance.ProfileParameters)(A κ m W:ℝ)(hm:0<m)
    {ρ:ℝ}(hκ:0≤κ)(hW:0≤W)(hρ:0<ρ)(hρhalf:ρ<1/2)(Bnext:ℝ≥0):
    0<constant P A κ m W hm hρ hρhalf Bnext:=by
  have ht:0≤NativeConvexGammaUniform.constant m W hm hρ hρhalf:=
    (NativeConvexGammaUniform.constant_pos m W hm hρ hρhalf).le
  have hs:=signed_nonneg P A
  have hl:=linear_nonneg P A κ m W hm hκ hW hρ hρhalf
  have hc:=clipped_nonneg P A κ W hκ hW hρ hρhalf
  have hk0:0≤max 1 (4:ℝ):=zero_le_one.trans (le_max_left _ _)
  have hk1:0≤max 1 (rootClip P κ Bnext):=zero_le_one.trans (le_max_left _ _)
  unfold constant
  positivity

/-- Actual numerical six-slot sharp caps collapse to one structural
constant, preserving the full frequency and the post-average clipping. -/
theorem sum_le (P:CanonicalCovariance.ProfileParameters)(A κ m W:ℝ)(hm:0<m)
    {ρ:ℝ}(hκ:0≤κ)(hW:0≤W)(hρ:0<ρ)(hρhalf:ρ<1/2)(Bnext:ℝ≥0)
    {X Y L e:ℝ}(hX:0≤X)(hY:0≤Y)(hL:0≤L)(he:0≤e):
    6*(NativeConvexGammaUniform.constant m W hm hρ hρhalf*signed P A*X+
      HaarWeightedHeat.higherConstant m W hm 0 ρ*MixedNativeFrozenFactorPositive.constant P A ρ*Y*L+
      weight κ W ρ*(GammaBandConstants.gradient P A ρ*Y*min 1 (4*e)+
        MixedNativeVarianceGammaTime.constant P A ρ*Y*L+
        GammaBandConstants.gradient P A ρ*Y*min 1 (rootClip P κ Bnext*e)+
        MixedNativeVarianceGammaTime.constant P A ρ*Y*L))≤
      constant P A κ m W hm hρ hρhalf Bnext*(X+Y*(L+min 1 e)):=by
  have ht:0≤NativeConvexGammaUniform.constant m W hm hρ hρhalf:=
    (NativeConvexGammaUniform.constant_pos m W hm hρ hρhalf).le
  have hs:=signed_nonneg P A
  have hl:=linear_nonneg P A κ m W hm hκ hW hρ hρhalf
  have hc:=clipped_nonneg P A κ W hκ hW hρ hρhalf
  have hb:=GammaClipCollapse.sum (mul_nonneg ht hs) hl hc hX hY hL he
    (K0:=4) (K1:=rootClip P κ Bnext)
  have hh:0≤X+Y*(L+min 1 e):=add_nonneg hX (mul_nonneg hY (add_nonneg hL (le_min zero_le_one he)))
  have hcstep:6*(NativeConvexGammaUniform.constant m W hm hρ hρhalf*signed P A+linear P A κ m W hm ρ+
      clipped P A κ W ρ*(max 1 (4:ℝ)+max 1 (rootClip P κ Bnext)))≤constant P A κ m W hm hρ hρhalf Bnext:=by
    unfold constant
    linarith
  have hend:=mul_le_mul_of_nonneg_right hcstep hh
  convert hb.trans hend using 1 <;> unfold linear clipped <;> ring
end SHE.JointGammaConstants
