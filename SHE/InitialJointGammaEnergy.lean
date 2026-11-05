module
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

namespace SHE.InitialJointGammaEnergy
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

def output(z:ℝ×Ω):CircleL2:=if ht:0<z.1∧z.1≤(h:ℝ) then
  NativeHeatObservation.embed (MixedNativeJointGammaOutput.value
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
    (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (v₀:=u₀) (S:=S) (P:=P) (hκP:=hκP) (v:=0) (b:=z.1.toNNReal)
    (hbH:=(Real.toNNReal_le_iff_le_coe.mpr ht.2).trans hhH)
    (hb1:=by
      rw [Real.coe_toNNReal _ ht.1.le]
      exact ht.2.trans ((show (h:ℝ)≤(H:ℝ) by exact_mod_cast hhH).trans hH))
    (hb0:=Real.toNNReal_pos.mpr ht.1) (hnull:=hnull) (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1)
    (ha:=ha) (hA:=hA) (hβ:=P.exponent_pos.le) (hβ1:=P.exponent_le_one) (hh:=hholder) (j:=j)
    (hΛ:=hL) (ρ:=ρ) (hρ:=hρ) (hρhalf:=hρhalf) z.2) else 0
local notation "Output"=>output
  (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (hκP:=hκP) (hH:=hH) (hnull:=hnull) (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1) (ha:=ha) (hA:=hA) (hρ:=hρ) (hρhalf:=hρhalf) (hholder:=hholder) (j:=j) (hL:=hL) (h:=h) (hhH:=hhH)

def energy(T:ℝ):ℝ≥0∞:=∫⁻ω,ENNReal.ofReal (‖Output (T,ω)‖^2) ∂μ
local notation "Energy"=>energy
  (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (hκP:=hκP) (hH:=hH) (hnull:=hnull) (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1) (ha:=ha) (hA:=hA) (hρ:=hρ) (hρhalf:=hρhalf) (hholder:=hholder) (j:=j) (hL:=hL) (h:=h) (hhH:=hhH)
local notation "CMass" T:max=>∫⁻τ in Set.Ioc (0:ℝ) T,∫⁻ω,ENNReal.ofReal
  (τ^(ρ-1/2)*‖NativeRandomRows.nativeRow (NativeJointRowClock.field P UU VV Λ 0 (T:ℝ).toNNReal a j 0) ((T-τ).toNNReal,ω)-
    NativeRandomRows.nativeRow (NativeJointRowClock.field P UU VV Λ 0 (T:ℝ).toNNReal a j 1) ((T-τ).toNNReal,ω)‖^2) ∂μ
local notation "SMass" T:max=>∫⁻τ in Set.Ioc (0:ℝ) T,MixedNativeSignedGammaRows.sectionEnergy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hL hρ.le A j 0 (T:ℝ).toNNReal τ
local notation "SignedCap"=>ENNReal.ofReal ((4*Real.pi^2)^(1/2:ℝ))*
  ENNReal.ofReal ((A*ScalarHeatBandEnvelope.constant P.exponent 0)^2*ScalarHeatBandTime.massConstant P.exponent 0*
    (ProfileVariance.lowerConstant*P.lower)⁻¹*CompactMollifier.radius (j+1)^(2*P.exponent))*Neg
local notation "CurrentCap"=>ENNReal.ofReal ((2*A*ScalarHeatGradientDifference.constant P.exponent)^2*
  ScalarHeatBandTime.massConstant P.exponent ρ*(ProfileVariance.lowerConstant*P.lower)^(-1-2*ρ)*
    CompactMollifier.radius (j+1)^(2*P.exponent+4*ρ)*min 1 (4*Global/CompactMollifier.radius (j+1)^2))

include hIJ₀ hIJ₁ hsmallL2 hBDGpast hBDG hlocal hBDGnext in
/-- Complete initial-strip ORIGINAL-I0/I1 joint Gamma, with both sharp
frequency terms and true original Global/Neg input energies. No early
output time, analytic Gamma budget or output version is assumed. -/
theorem complete_energy(hh:0<h)(hspan:(h:ℝ)≤P.horizon)
    (Bg:ℝ≥0)(hBDGg:StandardTerminalBDGPower 1 J Bg):
    (∫⁻T in Set.Ioc (0:ℝ) (h:ℝ),Energy T)≤
      6*(ENNReal.ofReal Trace*SignedCap+ENNReal.ofReal Ksum*CurrentCap):=by
  have hh1:(h:ℝ)≤1:=(show (h:ℝ)≤(H:ℝ) by exact_mod_cast hhH).trans hH
  have hi:=MixedMovingEnergy.global_integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    J hIJ₀ hIJ₁ (zero_le_one.trans hL) hH Bg hBDGg
  have hc:=InitialJointCurrentBudget.energy_measurable 𝓕 μ P H UU VV S.first_predictable S.second_predictable hi
    (zero_le_one.trans hL) (show (0:ℝ)<h by exact_mod_cast hh) hh1 (by linarith) hρhalf ha hA hholder j
  have hs:=InitialSignedGammaRows.energy (A:=A) 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hL hρ.le j h
  have hhR:(h:ℝ)≤(H:ℝ):=by exact_mod_cast hhH
  rw [min_eq_right hhR] at hc hs
  have hCM:AEMeasurable (fun T:ℝ=>ENNReal.ofReal Ksum*CMass T) (volume.restrict (Set.Ioc (0:ℝ) (h:ℝ))):=
    hc.2.const_mul _
  have hp(T:ℝ)(ht:T∈Set.Ioc (0:ℝ) (h:ℝ)):
      Energy T≤6*(ENNReal.ofReal Trace*SMass T+ENNReal.ofReal Ksum*CMass T):=by
    have hb:(T:ℝ).toNNReal≤H:=(Real.toNNReal_le_iff_le_coe.mpr ht.2).trans hhH
    have hwb:((T:ℝ).toNNReal:ℝ)≤P.horizon:=by rw [Real.coe_toNNReal _ ht.1.le];exact ht.2.trans hspan
    have he:=InitialJointGammaBudget.complete_energy
      (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
      (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (J:=J) (P:=P) (hκP:=hκP)
      (b:=(T:ℝ).toNNReal) (hbH:=hb) (hH:=hH) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (hb0:=Real.toNNReal_pos.mpr ht.1)
      (hsmallL2:=hsmallL2) (Bpast:=Bpast) (hBDGpast:=hBDGpast)
      (hnull:=hnull) (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1)
      (B:=B) (hBDG:=hBDG) (hlocal:=hlocal) (Bnext:=Bnext) (hBDGnext:=hBDGnext)
      (a:=a) (ha:=ha) (A:=A) (ρ:=ρ) (hA:=hA) (hρ:=hρ) (hρhalf:=hρhalf) (hholder:=hholder) (j:=j) (hL:=hL) hwb
    have hr:MixedNativeJointRowBudgets.timeBudget 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P hκP 0 (T:ℝ).toNNReal hb hH a j ρ 0 1=CMass T:=by
      simp only [MixedNativeJointRowBudgets.timeBudget,NNReal.coe_zero,sub_zero,Real.coe_toNNReal _ ht.1.le]
      rfl
    rw [hr] at he
    simp only [NNReal.coe_zero,sub_zero,Real.coe_toNNReal _ ht.1.le] at he
    dsimp only [energy,output]
    split_ifs with hT
    · exact he
    · exact False.elim (hT ht)
  calc
    _≤∫⁻T in Set.Ioc (0:ℝ) (h:ℝ),6*(ENNReal.ofReal Trace*SMass T+ENNReal.ofReal Ksum*CMass T):=by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with T ht
      exact hp T ht
    _=6*(ENNReal.ofReal Trace*(∫⁻T in Set.Ioc (0:ℝ) (h:ℝ),SMass T)+
        ENNReal.ofReal Ksum*(∫⁻T in Set.Ioc (0:ℝ) (h:ℝ),CMass T)):=by
      rw [lintegral_const_mul' _ _ (by norm_num: (6:ℝ≥0∞)≠∞),lintegral_add_right' _ hCM,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _≤_:=by
      gcongr <;> first | exact hs | exact hc.1
end SHE.InitialJointGammaEnergy
