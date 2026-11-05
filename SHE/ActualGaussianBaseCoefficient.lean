module
public import SHE.NativeBaseMasterCoefficient
public import SHE.ActualGaussianNegativeRMS
public import SHE.JointGammaActualConstantUniform
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.ActualGaussianBaseCoefficient
open Real
open scoped NNReal

def low(D:SmoothApproximation.ScalarData):ℝ:=
  ScalarHeatBandBernstein.amplitude D.cap D.holderConstant D.beta 1*LowBands.lowBandConstant D.beta

def frozen(D:SmoothApproximation.ScalarData)(P:CanonicalCovariance.ProfileParameters)(κ ρ:ℝ):ℝ:=
  sqrt (NativeFrozenBesselScale.constant (2-P.exponent) κ ρ*
    (2*D.holderConstant*GaussianHeatBandRootEnvelope.constant P.exponent)^2)*
    StateBands.rootConstant (P.exponent+2*ρ)

def inner(P:CanonicalCovariance.ProfileParameters)(κ:ℝ)(Bnext:ℝ≥0):ℝ:=
  2*(1+(Bnext:ℝ)*PastReferenceBracket.energyConstant P κ 1 0 1)

def gamma(D:SmoothApproximation.ScalarData)(P:CanonicalCovariance.ProfileParameters)
    (κ ell M:ℝ)(hell:0<ell)(hκP:κ<P.lower){ρ:ℝ}(hρ:0<ρ)(hρhalf:ρ<1/2)(Bnext:ℝ≥0):ℝ:=
  sqrt (2*JointGammaConstants.nativeConstant P D.holderConstant κ ell M hell hκP hρ hρhalf Bnext)

def leaf(D:SmoothApproximation.ScalarData)(Q:CanonicalCovariance.ProfileParameters)
    (κ M H:ℝ)(N:ℕ)(ηleaf:ℝ)(order:ℕ)(Bleaf B1 Bcov:ℝ≥0):ℝ:=
  sqrt (FullRemainderConstants.comparison Q κ M H (N+1) (D.beta/2) ηleaf order Bleaf B1 Bcov)*
    CanonicalGaussianRootBands.amplitude D 1 (N+2)*(2:ℝ)^(D.beta/2+ηleaf)*(16/15:ℝ)

def constant(D:SmoothApproximation.ScalarData)(P Q:CanonicalCovariance.ProfileParameters)
    (κ ell M H:ℝ)(hell:0<ell)(hκP:κ<P.lower){ρ:ℝ}(hρ:0<ρ)(hρhalf:ρ<1/2)
    (N:ℕ)(ηleaf:ℝ)(order:ℕ)(Bleaf B1 Bcov Bnext:ℝ≥0):ℝ:=
  NativeBaseMasterCoefficient.constant D.beta (low D) (frozen D P κ ρ) (inner P κ Bnext)
    (gamma D P κ ell M hell hκP hρ hρhalf Bnext) (leaf D Q κ M H N ηleaf order Bleaf B1 Bcov)

theorem constant_pos(D:SmoothApproximation.ScalarData)(P Q:CanonicalCovariance.ProfileParameters)
    (κ ell M H:ℝ)(hell:0<ell)(hκP:κ<P.lower){ρ:ℝ}(hρ:0<ρ)(hρhalf:ρ<1/2)
    (N:ℕ)(ηleaf:ℝ)(order:ℕ)(Bleaf B1 Bcov Bnext:ℝ≥0):
    0<constant D P Q κ ell M H hell hκP hρ hρhalf N ηleaf order Bleaf B1 Bcov Bnext:=
  NativeBaseMasterCoefficient.constant_pos _ _ _ _ _ _

private theorem root_nonneg{a:ℝ}(ha:0<a)(ha1:a<1):0≤StateBands.rootConstant a:=by
  unfold StateBands.rootConstant StateBands.geometricConstant
  have h0:=DyadicTransport.smoothingConstant_pos (show 0<1-a by linarith) (show 1-a<1 by linarith)
  have h1:0≤(1-(2:ℝ)^(-a))⁻¹:=inv_nonneg.mpr (by linarith [(StateBands.geometric_ratio ha).2])
  exact add_nonneg h0.le h1

/-- Concrete low/frozen/Gamma/leaf RHS of the actual stochastic bound,
with its genuine current energy E and the structural common constant. -/
theorem cap(D:SmoothApproximation.ScalarData)(P Q:CanonicalCovariance.ProfileParameters)
    (κ ell M H:ℝ)(hell:0<ell)(hκP:κ<P.lower){ρ:ℝ}(hρ:0<ρ)(hρhalf:ρ<1/2)
    (N:ℕ)(ηleaf:ℝ)(order:ℕ)(Bleaf B1 Bcov Bnext:ℝ≥0)
    (hβ:P.exponent=D.beta)(hρeq:ρ=SHE.rho D.beta)(hβsmall:D.beta≤4/25)
    {Λ E K:ℝ}(hΛ:1≤Λ)(hE:0≤E)(hK:0≤K)(J:ℕ)
    (hlow:(2:ℝ)^J≤2*Λ^(1/4:ℝ))(hhigh:Λ^(1/4:ℝ)≤(2:ℝ)^(J+1)):
    ((ScalarHeatBandBernstein.amplitude D.cap D.holderConstant D.beta 1*LowBands.lowBandConstant D.beta)*
      Λ^(-ρ/2))*((2:ℝ)^J)^(1-D.beta)*sqrt E+
    sqrt (NativeFrozenBesselScale.constant (2-P.exponent) κ ρ*
      (2*D.holderConstant*GaussianHeatBandRootEnvelope.constant P.exponent)^2)*
      StateBands.rootConstant (P.exponent+2*ρ)*
      (sqrt ((2*(1+(Bnext:ℝ)*PastReferenceBracket.energyConstant P κ 1 0 1))*E))^(P.exponent+2*ρ)+
    sqrt (2*JointGammaConstants.nativeConstant P D.holderConstant κ ell M hell hκP hρ hρhalf Bnext)*
      (StateBands.geometricConstant P.exponent*Λ^(-P.exponent/4)*K+
        StateBands.rootConstant (GammaDyadicWindowScale.alpha P.exponent ρ)*
          (sqrt E)^(GammaDyadicWindowScale.alpha P.exponent ρ)+
        StateBands.geometricConstant (GammaDyadicWindowScale.degree P.exponent ρ)*
          Λ^(-GammaDyadicWindowScale.degree P.exponent ρ/4)*sqrt E)+
    Λ^(-ρ/2)*sqrt (FullRemainderConstants.comparison Q κ M H (N+1) (P.exponent/2) ηleaf order Bleaf B1 Bcov)*
      CanonicalGaussianRootBands.amplitude D 1 (N+2)*(2:ℝ)^(D.beta/2+ηleaf)*(16/15:ℝ)*
      ((2:ℝ)^(J+1))^(-4:ℝ)*E^((P.exponent/2)/2)≤
      constant D P Q κ ell M H hell hκP hρ hρhalf N ηleaf order Bleaf B1 Bcov Bnext*
        (Λ^(-D.beta/4)*K+SHE.linearM D.beta (SHE.depth D.beta) Λ*sqrt E+
          ActualReferenceMasterClosure.rows D.beta Λ (sqrt E) 0 0):=by
  have ha:=SHE.admissible_parameters D.beta D.beta_pos hβsmall
  have hlc:0≤low D:=by
    unfold low LowBands.lowBandConstant
    have hp:1<(2:ℝ)^(1-D.beta):=by
      simpa using rpow_lt_rpow_of_exponent_lt (by norm_num:(1:ℝ)<2) (show 0<1-D.beta by linarith)
    exact mul_nonneg (ScalarHeatBandBernstein.amplitude_nonneg D.holderConstant_nonneg 1)
      (div_nonneg (rpow_nonneg (by norm_num:(0:ℝ)≤2) _) (by linarith))
  have hfc:0≤frozen D P κ ρ:=by
    unfold frozen
    exact mul_nonneg (sqrt_nonneg _) (root_nonneg (by rw [hβ,hρeq];exact ha.2.2.2.2.1)
      (by rw [hβ,hρeq];exact ha.2.2.2.2.2.1))
  have hic:0 ≤ inner P κ Bnext:=by
    unfold inner
    have hc:=PastReferenceBracket.energyConstant_nonneg P hκP (by norm_num:(0:ℝ)≤1) 1 0
    positivity
  have hgc:0≤gamma D P κ ell M hell hκP hρ hρhalf Bnext:=sqrt_nonneg _
  have hleaf:0≤leaf D Q κ M H N ηleaf order Bleaf B1 Bcov:=by
    unfold leaf
    have hA:=CanonicalGaussianRootBands.amplitude_nonneg D (W:=1) zero_le_one (N+2)
    positivity
  have hh:=NativeBaseMasterCoefficient.energy_cap J (low D) (frozen D P κ ρ) (inner P κ Bnext)
    (gamma D P κ ell M hell hκP hρ hρhalf Bnext) (leaf D Q κ M H N ηleaf order Bleaf B1 Bcov)
    D.beta_pos hβsmall hΛ hE hK hlc hfc hic hgc hleaf hlow hhigh
  convert hh using 1 <;>
    simp only [constant,low,frozen,inner,gamma,leaf,hβ,hρeq,
      GammaDyadicWindowScale.degree_eq,GammaDyadicWindowScale.alpha,SHE.alpha]
  · congr 1
    ring

/-- Every numerical profile entry is unchanged by canonical smoothing,
including the common min/max ellipticity Gamma constant. -/
theorem constant_congr(D:SmoothApproximation.ScalarData)(P P' Q:CanonicalCovariance.ProfileParameters)
    (hl:P.lower=P'.lower)(hu:P.upper=P'.upper)(hH:P.holder=P'.holder)(hβ:P.exponent=P'.exponent)
    (κ ell M H:ℝ)(hell:0<ell)(hκP:κ<P.lower)(hκP':κ<P'.lower)
    {ρ:ℝ}(hρ:0<ρ)(hρhalf:ρ<1/2)(N:ℕ)(ηleaf:ℝ)(order:ℕ)(Bleaf B1 Bcov Bnext:ℝ≥0):
    constant D P Q κ ell M H hell hκP hρ hρhalf N ηleaf order Bleaf B1 Bcov Bnext=
      constant D P' Q κ ell M H hell hκP' hρ hρhalf N ηleaf order Bleaf B1 Bcov Bnext:=by
  have he:PastReferenceBracket.energyConstant P κ 1 0 1=PastReferenceBracket.energyConstant P' κ 1 0 1:=by
    unfold PastReferenceBracket.energyConstant
    rw [hl,hu,hH,hβ]
  unfold constant frozen inner gamma
  rw [hβ,he,JointGammaConstants.native_constant_congr P P' hl hu hH hβ
    D.holderConstant κ ell M hell hκP hκP' hρ hρhalf Bnext]

variable (D:SmoothApproximation.ScalarData){T:ℝ}(hT:0<T)(hT1:T≤1)
  (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2)
local notation "Smooth"=>ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall
local notation "Rough"=>ControlledSmoothLimit.roughTotalParameters D hT hT1 hsmall

theorem smooth_constant(Q:CanonicalCovariance.ProfileParameters)
    (κ ell M H:ℝ)(hell:0<ell){ρ:ℝ}(hρ:0<ρ)(hρhalf:ρ<1/2)
    (N:ℕ)(ηleaf:ℝ)(order:ℕ)(Bleaf B1 Bcov Bnext:ℝ≥0)(n k:ℕ)
    (hκn:κ<(Smooth n).lower)(hκk:κ<(Smooth k).lower):
    constant D (Smooth n) Q κ ell M H hell hκn hρ hρhalf N ηleaf order Bleaf B1 Bcov Bnext=
      constant D (Smooth k) Q κ ell M H hell hκk hρ hρhalf N ηleaf order Bleaf B1 Bcov Bnext:=by
  apply constant_congr <;> rfl

theorem smooth_rough_constant
    (κ ell M H:ℝ)(hell:0<ell){ρ:ℝ}(hρ:0<ρ)(hρhalf:ρ<1/2)
    (N:ℕ)(ηleaf:ℝ)(order:ℕ)(Bleaf B1 Bcov Bnext:ℝ≥0)(n:ℕ)
    (hκn:κ<(Smooth n).lower)(hκR:κ<(Rough).lower):
    constant D (Smooth n) Rough κ ell M H hell hκn hρ hρhalf N ηleaf order Bleaf B1 Bcov Bnext=
      constant D Rough Rough κ ell M H hell hκR hρ hρhalf N ηleaf order Bleaf B1 Bcov Bnext:=by
  apply constant_congr <;> rfl
end SHE.ActualGaussianBaseCoefficient
