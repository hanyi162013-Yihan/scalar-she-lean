module
public import SHE.JointGammaConstants
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.GammaENNRealCollapse
open Real
open scoped NNReal ENNReal

/-- Exact finite-energy normalization of the six positive caps. -/
theorem ofReal_budget {Cs Cf K S F C V R:ℝ}
    (hCs:0≤Cs)(hCf:0≤Cf)(hK:0≤K)(hS:0≤S)(hF:0≤F)(hC:0≤C)(hV:0≤V)(hR:0≤R):
    (6:ℝ≥0∞)*(ENNReal.ofReal Cs*ENNReal.ofReal S+ENNReal.ofReal Cf*ENNReal.ofReal F+
      ENNReal.ofReal K*(ENNReal.ofReal C+ENNReal.ofReal V+ENNReal.ofReal R+ENNReal.ofReal V))=
        ENNReal.ofReal (6*(Cs*S+Cf*F+K*(C+V+R+V))):=by
  symm
  rw [ENNReal.ofReal_mul (by norm_num:0≤(6:ℝ))]
  norm_num only [ENNReal.ofReal_ofNat]
  rw [ENNReal.ofReal_add (add_nonneg (mul_nonneg hCs hS) (mul_nonneg hCf hF))
    (mul_nonneg hK (add_nonneg (add_nonneg (add_nonneg hC hV) hR) hV)),
    ENNReal.ofReal_add (mul_nonneg hCs hS) (mul_nonneg hCf hF),
    ENNReal.ofReal_mul hCs,ENNReal.ofReal_mul hCf,ENNReal.ofReal_mul hK,
    ENNReal.ofReal_add (add_nonneg (add_nonneg hC hV) hR) hV,
    ENNReal.ofReal_add (add_nonneg hC hV) hR,ENNReal.ofReal_add hC hV]

/-- Collapse the exact native six-slot frequency caps, including the
original finite negative-energy integral, into one structural constant.
No damping, time, frequency, smooth-derivative or stochastic bound is
inserted here; those quantities have already been proved in the slots. -/
theorem sharp (P:CanonicalCovariance.ProfileParameters)(A κ m W:ℝ)(hm:0<m)
    {ρ:ℝ}(hκ:0≤κ)(hκP:κ<P.lower)(hW:0≤W)(hρ:0<ρ)(hρhalf:ρ<1/2)(Bnext:ℝ≥0)
    {r h E:ℝ}(hr:0<r)(hh:0<h)(hE:0≤E)(Neg:ℝ≥0∞)(hNeg:Neg≠∞):
    let β:=P.exponent
    let pow:=r^(2*β+4*ρ)
    let age:=h^((β-1)/2)
    let Cgrad:=GammaBandConstants.gradient P A ρ
    let Cvar:=MixedNativeVarianceGammaTime.constant P A ρ
    let Cfactor:=MixedNativeFrozenFactorPositive.constant P A ρ
    let Higher:=HaarWeightedHeat.higherConstant m W hm 0 ρ
    let Trace:=NativeConvexGammaUniform.constant m W hm hρ hρhalf
    let K:=JointGammaConstants.weight κ W ρ
    let Kr:=JointGammaConstants.rootClip P κ Bnext
    (6:ℝ≥0∞)*(ENNReal.ofReal Trace*(ENNReal.ofReal ((4*π^2)^(1/2:ℝ))*
        ENNReal.ofReal ((A*ScalarHeatBandEnvelope.constant β 0)^2*ScalarHeatBandTime.massConstant β 0*
          (ProfileVariance.lowerConstant*P.lower)⁻¹*r^(2*β))*Neg)+
      ENNReal.ofReal Higher*ENNReal.ofReal (Cfactor*pow*age*E)+
      ENNReal.ofReal K*(ENNReal.ofReal (Cgrad*pow*min 1 (4*E/r^2))+
        ENNReal.ofReal (Cvar*pow*age*E)+ENNReal.ofReal (Cgrad*pow*min 1 (Kr*E/r^2))+
        ENNReal.ofReal (Cvar*pow*age*E)))≤
      ENNReal.ofReal (JointGammaConstants.constant P A κ m W hm hρ hρhalf Bnext*
        (r^(2*β)*Neg.toReal+pow*(age*E+min 1 (E/r^2)))):=by
  intro β pow age Cgrad Cvar Cfactor Higher Trace K Kr
  have hρ0:-(1/2:ℝ)<ρ:=by linarith
  have ht:0≤Trace:=(NativeConvexGammaUniform.constant_pos m W hm hρ hρhalf).le
  have hhi:0≤Higher:=GammaBandConstants.higher_nonneg m W hm hρ hρhalf
  have hk:0≤K:=JointGammaConstants.weight_nonneg hκ hW hρhalf
  have hkr:0≤Kr:=GammaBandConstants.reference_clip_nonneg P hκP Bnext
  have hcg:0≤Cgrad:=GammaBandConstants.gradient_nonneg P A hρ0 hρhalf
  have hcv:0≤Cvar:=GammaBandConstants.variance_nonneg P A hρ0 hρhalf
  have hcf:0≤Cfactor:=GammaBandConstants.frozen_factor_nonneg P A hρ0 hρhalf
  have hp:0≤pow:=Real.rpow_nonneg hr.le _
  have ha:0≤age:=Real.rpow_nonneg hh.le _
  have hcl0:0≤min 1 (4*E/r^2):=le_min zero_le_one (div_nonneg (by positivity) (sq_nonneg _))
  have hcl1:0≤min 1 (Kr*E/r^2):=le_min zero_le_one (div_nonneg (mul_nonneg hkr hE) (sq_nonneg _))
  have hs:0≤JointGammaConstants.signed P A:=JointGammaConstants.signed_nonneg P A
  have hclock:0≤(4*π^2)^(1/2:ℝ):=by positivity
  have hmass:0≤ScalarHeatBandTime.massConstant β 0:=(GammaBandConstants.mass_pos P (by norm_num) (by norm_num)).le
  have hc:=mul_pos ProfileVariance.lowerConstant_pos P.lower_pos
  have hband:0≤(A*ScalarHeatBandEnvelope.constant β 0)^2*ScalarHeatBandTime.massConstant β 0*
      (ProfileVariance.lowerConstant*P.lower)⁻¹*r^(2*β):=by positivity
  have hsign:ENNReal.ofReal ((4*π^2)^(1/2:ℝ))*
      ENNReal.ofReal ((A*ScalarHeatBandEnvelope.constant β 0)^2*ScalarHeatBandTime.massConstant β 0*
        (ProfileVariance.lowerConstant*P.lower)⁻¹*r^(2*β))*Neg=
      ENNReal.ofReal (JointGammaConstants.signed P A*r^(2*β)*Neg.toReal):=by
    calc
      _=ENNReal.ofReal ((4*π^2)^(1/2:ℝ))*
          ENNReal.ofReal ((A*ScalarHeatBandEnvelope.constant β 0)^2*ScalarHeatBandTime.massConstant β 0*
            (ProfileVariance.lowerConstant*P.lower)⁻¹*r^(2*β))*ENNReal.ofReal Neg.toReal:=by
        rw [ENNReal.ofReal_toReal hNeg]
      _=ENNReal.ofReal (((4*π^2)^(1/2:ℝ))*
          ((A*ScalarHeatBandEnvelope.constant β 0)^2*ScalarHeatBandTime.massConstant β 0*
            (ProfileVariance.lowerConstant*P.lower)⁻¹*r^(2*β))*Neg.toReal):=by
        rw [ENNReal.ofReal_mul (mul_nonneg hclock hband),ENNReal.ofReal_mul hclock]
      _=_:=congrArg ENNReal.ofReal (by dsimp only [JointGammaConstants.signed,β];ring)
  rw [hsign,ofReal_budget ht hhi hk
    (mul_nonneg (mul_nonneg hs (Real.rpow_nonneg hr.le _)) ENNReal.toReal_nonneg)
    (by positivity) (by positivity) (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hb:=JointGammaConstants.sum_le P A κ m W hm hκ hW hρ hρhalf Bnext
    (X:=r^(2*β)*Neg.toReal) (Y:=pow) (L:=age*E) (e:=E/r^2)
    (mul_nonneg (Real.rpow_nonneg hr.le _) ENNReal.toReal_nonneg) hp (mul_nonneg ha hE)
    (div_nonneg hE (sq_nonneg _))
  simpa only [mul_div_assoc,mul_assoc] using hb
end SHE.GammaENNRealCollapse
