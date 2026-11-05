module
public import SHE.InitialJointGammaEnergy
public import SHE.GammaENNRealCollapse
public import SHE.JointGammaActualConstantUniform
public import SHE.InitialJointGammaBudget
public import SHE.MixedNativeJointGammaOutput
public import SHE.InitialJointCurrentBudget
public import SHE.InitialSignedGammaRows
public import SHE.MixedMovingEnergy
public import SHE.InitialJointGammaZeroBudgets
public import SHE.MixedNativeJointGammaPhysicalBudget
public import SHE.InitialNativeColumnEnergy
public import SHE.MixedNativeJointRowBudgets
public import SHE.MixedNativeFrozenFactorPositive
public import SHE.JointGammaFrozenCanonical
public import SHE.JointGammaRootHilbertPair
public import SHE.FirstGammaTerminalReferenceEnergy
public import SHE.JointGammaRootScalarPair
public import SHE.JointGammaOriginalHilbert
public import SHE.NativeBesselDifferenceIdentity
public import SHE.NativeBesselFiniteIdentity
public import SHE.MixedNativePairedRootZero
public import SHE.JointGammaRootRecursion
public import SHE.ControlledScalarReference
public import SHE.JointGammaActualEndpointPair
public import SHE.JointGammaFirstPairRecursion
public import SHE.JointGammaOriginalRegrouping

public import SHE.JointGammaEndpointCurrentNative
public import SHE.FirstGammaEndpointReferenceNative
public import SHE.NativeJointCurrentEndpoint
public import SHE.JointGammaEndpointValues
public import SHE.JointGammaOriginalIto
public import SHE.JointGammaNativeInput
public import SHE.JointGammaEndpointIto
public import SHE.JointGammaNativeRaw
public import SHE.JointGammaNativeNoise
public import SHE.NativeGammaDamping
public import SHE.JointGammaNativeGradients
public import SHE.JointGammaNativeRows
public import SHE.JointGammaScalarNoise
public import SHE.NativeJointPhysicalGammaAlgebra
public import SHE.JointGammaNativeCurrentTime
public import SHE.JointGammaNativeReferenceTime
public import SHE.NativeCanonicalVarianceIdentity
public import SHE.NativeJointGammaFields
public import SHE.JointGammaCurrentTime
public import SHE.NativeJointCurrentSections
public import SHE.JointGammaCurrentIdentity
public import SHE.NativeJointGammaCurrent
public import SHE.JointInterpolationFields
public import SHE.ScalarCovarianceTailScale
public import SHE.NativeScalarProductAlgebra
public import SHE.JointGammaAffine
public import SHE.FirstGammaEndpointPhysical
public import SHE.FirstGammaEndpointCoherence
public import SHE.FirstGammaCurrentIdentity
public import SHE.FirstGammaEndpointConstruction
public import SHE.FirstGammaConstruction
public import SHE.FirstGammaRows
public import SHE.RescaledRowsCoherence
public import SHE.FiniteSpliceStopCoherence
public import SHE.FirstGammaEndpointRows
public import SHE.SingularReferenceSplice
public import SHE.FullHorizonEndpointVersion
public import SHE.SingularInputBounds
public import SHE.MixedNativeFrozenPrefixIto
public import SHE.FirstGammaAffine
public import SHE.MixedNativeFrozenInterpolationRows
public import SHE.MixedNativeFrozenPrefixValues
public import SHE.FiniteReferenceSplicePast
public import SHE.StoppedInputAlgebra
public import SHE.PastFrozenPrefixRows
public import SHE.MixedPastJointData
public import SHE.FiniteReferenceSplice
public import SHE.MixedNativeJointPhysical
public import SHE.MixedNativePairMartingale
public import SHE.MixedNativeJointObservation
public import SHE.NativeJointPhysicalRows
public import SHE.NativeJointBracketDefect
public import SHE.NativeJointCovariance
public import SHE.NativeJointPhysicalStep

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.InitialJointGammaSharpEnergy
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance jointGammaOriginalIto_realSigma : MeasurableSpace RealL2 := borel _
local instance jointGammaOriginalIto_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance jointGammaOriginalIto_circleSigma : MeasurableSpace CircleL2 := borel _
local instance jointGammaOriginalIto_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance jointGammaOriginalIto_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance jointGammaOriginalIto_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance jointGammaOriginalIto_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance jointGammaOriginalIto_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (P:CanonicalCovariance.ProfileParameters) (hκP:κ<P.lower) (hΛ:0≤Λ) (b:ℝ≥0) (hbH:b≤H) (hH:(H:ℝ)≤1)
variable (B:ℝ≥0) (hBDG:StandardTerminalBDG16 J B)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable  (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
variable (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1)
variable (hsmallL2:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (Bpast:ℝ≥0) (hBDGpast:StandardTerminalBDGPower 2 J Bpast)
variable (hlocal:StandardTerminalPastLocality I₁) (Bnext:ℝ≥0) (hBDGnext:StandardTerminalBDGPower 1 I₁ Bnext)
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {a:ℝ→ℝ}(ha:SmoothCylinders.BoundedSmooth a){A ρ:ℝ}(hA:0≤A)
variable (hρ:0<ρ)(hρhalf:ρ<1/2)(hholder:∀x y,|a x-a y|≤A*|x-y|^P.exponent)(j:ℕ)(hL:1≤Λ)
local notation "Lower"=>MixedNativeGammaEnergy.commonLower (ell:=ell) (P:=P) (κ:=κ)
local notation "Upper"=>MixedNativeGammaEnergy.commonUpper (M:=M) (P:=P) (κ:=κ)
local notation "hm"=>MixedNativeGammaEnergy.commonLower_pos (ell:=ell) (P:=P) (κ:=κ) (hell:=hell) (hκP:=hκP)
local notation "Trace"=>NativeConvexGammaUniform.constant Lower Upper hm hρ hρhalf
local notation "Ksum"=>(κ+Upper)*(1+2*HeatTrace.fractionalGaussianIntegral ρ)

variable (h:ℝ≥0)(hhH:h≤H)
local notation "UU"=>Function.uncurry S.first
local notation "VV"=>Function.uncurry S.second
local notation "Global"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Neg"=>MixedActualEnergyBridge.negativeEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ρ

local notation "Energy"=>InitialJointGammaEnergy.energy (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (hκP:=hκP) (hH:=hH) (hnull:=hnull) (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1) (ha:=ha) (hA:=hA) (hρ:=hρ) (hρhalf:=hρhalf) (hholder:=hholder) (j:=j) (hL:=hL) (h:=h) (hhH:=hhH)
local notation "Radius"=>CompactMollifier.radius (j+1)
local notation "Cgamma"=>JointGammaConstants.nativeConstant P A κ ell M hell hκP hρ hρhalf Bnext

include hIJ₀ hIJ₁ hsmallL2 hBDGpast hBDG hlocal hBDGnext in
/-- The COMPLETE genuine initial Gamma obeys the SAME structural
constant and master-row frequency cap as completed windows. The
additional nonnegative past terms only enlarge the proved sharp cap. -/
theorem complete_energy(hh:0<h)(hspan:(h:ℝ)≤P.horizon)
    (Bg:ℝ≥0)(hBDGg:StandardTerminalBDGPower 1 J Bg):
    (∫⁻T in Set.Ioc (0:ℝ) (h:ℝ),Energy T)≤ENNReal.ofReal (Cgamma*
      (Radius^(2*P.exponent)*(Neg).toReal+Radius^(2*P.exponent+4*ρ)*
        ((h:ℝ)^((P.exponent-1)/2)*Global+min 1 (Global/Radius^2)))):=by
  have hbase:=InitialJointGammaEnergy.complete_energy
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
    (I₀:=I₀) (I₁:=I₁) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (u₀:=u₀) (S:=S) (J:=J) (P:=P) (hκP:=hκP) (hH:=hH)
    (hsmallL2:=hsmallL2) (Bpast:=Bpast) (hBDGpast:=hBDGpast)
    (hnull:=hnull) (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1)
    (B:=B) (hBDG:=hBDG) (hlocal:=hlocal) (Bnext:=Bnext) (hBDGnext:=hBDGnext)
    (a:=a) (ha:=ha) (A:=A) (ρ:=ρ) (hA:=hA) (hρ:=hρ) (hρhalf:=hρhalf) (hholder:=hholder) (j:=j) (hL:=hL)
    (h:=h) (hhH:=hhH) hh hspan Bg hBDGg
  have hUpper:0≤Upper:=by
    have hp:P.lower≤P.upper:=(P.lower_bound 0).trans (P.upper_bound 0)
    exact (sub_pos.mpr (hκP.trans_le hp)).le.trans (le_max_right _ _)
  have hNeg:Neg≠∞:=ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    (MixedActualEnergyBridge.negative_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      (zero_lt_one.trans_le hL) hρ.le)
  have hsharp:=GammaENNRealCollapse.sharp P A κ Lower Upper hm hκ.le hκP hUpper hρ hρhalf Bnext
    (CompactMollifier.radius_pos (j+1)) (show (0:ℝ)<h by exact_mod_cast hh)
    (MixedMovingEnergy.globalEnergy_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S) Neg hNeg
  apply hbase.trans (le_trans ?_ hsharp)
  let SG:ℝ≥0∞:=ENNReal.ofReal Trace*(ENNReal.ofReal ((4*Real.pi^2)^(1/2:ℝ))*
    ENNReal.ofReal ((A*ScalarHeatBandEnvelope.constant P.exponent 0)^2*ScalarHeatBandTime.massConstant P.exponent 0*
      (ProfileVariance.lowerConstant*P.lower)⁻¹*Radius^(2*P.exponent))*Neg)
  let CC:ℝ≥0∞:=ENNReal.ofReal (GammaBandConstants.gradient P A ρ*Radius^(2*P.exponent+4*ρ)*min 1 (4*Global/Radius^2))
  let VarCap:ℝ≥0∞:=ENNReal.ofReal (MixedNativeVarianceGammaTime.constant P A ρ*Radius^(2*P.exponent+4*ρ)*
    (h:ℝ)^((P.exponent-1)/2)*Global)
  let RR:ℝ≥0∞:=ENNReal.ofReal (GammaBandConstants.gradient P A ρ*Radius^(2*P.exponent+4*ρ)*
    min 1 (JointGammaConstants.rootClip P κ Bnext*Global/Radius^2))
  let FF:ℝ≥0∞:=ENNReal.ofReal (HaarWeightedHeat.higherConstant Lower Upper hm 0 ρ)*
    ENNReal.ofReal (MixedNativeFrozenFactorPositive.constant P A ρ*Radius^(2*P.exponent+4*ρ)*
      (h:ℝ)^((P.exponent-1)/2)*Global)
  let KK:ℝ≥0∞:=ENNReal.ofReal Ksum
  change (6:ℝ≥0∞)*(SG+KK*CC)≤6*(SG+FF+KK*(CC+VarCap+RR+VarCap))
  have hC:CC≤CC+VarCap+RR+VarCap:=by
    calc
      _≤CC+VarCap:=le_add_of_nonneg_right bot_le
      _≤CC+VarCap+RR:=le_add_of_nonneg_right bot_le
      _≤CC+VarCap+RR+VarCap:=le_add_of_nonneg_right bot_le
  have hS:SG+KK*CC≤SG+FF+KK*(CC+VarCap+RR+VarCap):=by
    calc
      _≤SG+FF+KK*CC:=add_le_add_left (le_add_of_nonneg_right bot_le) _
      _≤_:=add_le_add_right (mul_le_mul_right hC KK) _
  exact mul_le_mul_right hS 6
end SHE.InitialJointGammaSharpEnergy
