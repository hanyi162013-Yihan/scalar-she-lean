module

public import SHE.MixedNativeJointRowBudgets
public import SHE.MixedNativeJointGammaOuter
public import SHE.GammaEnvelopeIntegral
public import SHE.MixedNativeJointEnvelopeEnergy
public import SHE.MixedNativeJointGammaEnvelope
public import SHE.MixedNativeMovingJointBudgets
public import SHE.MixedNativeJointSlotEnvelopes
public import SHE.MixedNativeJointGammaOutput
public import SHE.MixedNativeJointGammaPhysicalBudget
public import SHE.MixedNativeSignedBudget
public import SHE.MixedNativeJointDirectBudget
public import SHE.MixedNativeMovingFrozenFactor
public import SHE.MixedNativePastBudget
public import SHE.GammaBandConstants
public import SHE.NativeMovingGammaClock
public import SHE.MixedMovingEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
namespace SHE.MixedNativeJointGammaIntegral
open Set MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance mixedNativeMovingCurrentGamma_realSigma : MeasurableSpace RealL2:=borel _
local instance mixedNativeMovingCurrentGamma_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance mixedNativeMovingCurrentGamma_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance mixedNativeMovingCurrentGamma_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance mixedNativeMovingCurrentGamma_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance mixedNativeMovingCurrentGamma_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance mixedNativeMovingCurrentGamma_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedNativeMovingCurrentGamma_blockSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedNativeMovingCurrentGamma_blockBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance mixedNativeMovingCurrentGamma_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance mixedNativeMovingCurrentGamma_columnsBorel : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
local instance mixedNativeMovingCurrentGamma_unitPos : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance mixedNativeMovingCurrentGamma_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance mixedNativeMovingCurrentGamma_realSecond : SecondCountableTopology RealL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)



variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hΛ : 0≤Λ) (hH : (H:ℝ)≤1) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower 1 J B)
variable (P:CanonicalCovariance.ProfileParameters) (hκP:κ<P.lower)
variable (h W:ℝ) (hh:0<h) (hhP:h≤P.horizon) (hW0:0≤W) (hcover:W+h≤H)
variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (Bpast:ℝ≥0) (hBDGpast:StandardTerminalBDGPower 2 J Bpast)

local notation "Past"=>NativeMovingGammaClock.past W
local notation "Terminal"=>NativeMovingGammaClock.terminal W h
local notation "covered" r=>NativeMovingGammaClock.terminal_le hW0 hh.le H hcover r
local notation "ordered" r=>NativeMovingGammaClock.past_lt hW0 hh r
local notation "span" r=>NativeMovingGammaClock.span hW0 hh.le r
local notation "Global"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

local notation "Budget"=>MixedNativeMovingJointBudgets.budget 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hH P hκP h W hh hW0 hcover
local notation "Factor"=>MixedNativeMovingFrozenFactor.budget 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP h W
local notation "E" r=>MixedMovingEnergy.energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S (r:ℝ).toNNReal

variable (hL:1≤Λ) {a:ℝ→ℝ} (ha:SmoothCylinders.BoundedSmooth a) {A ρ:ℝ} (hA:0≤A)
variable (hρ:0<ρ) (hρhalf:ρ<1/2) (hholder:∀x y,|a x-a y|≤A*|x-y|^P.exponent) (j:ℕ)
variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
variable (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1)
local notation "Lower"=>MixedNativeGammaEnergy.commonLower (ell:=ell) (P:=P) (κ:=κ)
local notation "Upper"=>MixedNativeGammaEnergy.commonUpper (M:=M) (P:=P) (κ:=κ)
local notation "LowerPos"=>MixedNativeGammaEnergy.commonLower_pos (ell:=ell) (P:=P) (κ:=κ) (hell:=hell) (hκP:=hκP)
local notation "Trace"=>NativeConvexGammaUniform.constant Lower Upper LowerPos hρ hρhalf
local notation "Higher"=>HaarWeightedHeat.higherConstant Lower Upper LowerPos 0 ρ
local notation "Ksum"=>(κ+Upper)*(1+2*HeatTrace.fractionalGaussianIntegral ρ)
local notation "Signed"=>MixedNativeSignedBudget.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hL hρ.le A j h
local notation "Direct"=>MixedNativeJointDirectBudget.direct 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P h a j ρ
local notation "Variance"=>MixedNativeJointSlotEnvelopes.variance 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P h A ρ j
local notation "FactorEnvelope"=>MixedNativeJointSlotEnvelopes.factor 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P h A ρ j
local notation "Root"=>MixedNativeJointSlotEnvelopes.root 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P A ρ j

local notation "Energy"=>MixedNativeJointGammaEnvelope.energy (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
    (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (hκP:=hκP) (hH:=hH)
    (hh:=hh) (hW0:=hW0) (hcover:=hcover) (h:=h) (W:=W) (hL:=hL)
    (ha:=ha) (hA:=hA) (hρ:=hρ) (hρhalf:=hρhalf) (hholder:=hholder) (j:=j)
    (hnull:=hnull) (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1)
local notation "Value"=>MixedNativeJointGammaEnvelope.value (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
    (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (hκP:=hκP) (h:=h)
    (hL:=hL) (A:=A) (ρ:=ρ) (hρ:=hρ) (hρhalf:=hρhalf) (j:=j)
    (a:=a)

variable (Bγ:ℝ≥0) (hBDGγ:StandardTerminalBDG16 J Bγ)
variable (hlocal:StandardTerminalPastLocality I₁) (Bnext:ℝ≥0) (hBDGnext:StandardTerminalBDGPower 1 I₁ Bnext)
local notation "Radius"=>CompactMollifier.radius (j+1)
local notation "Neg"=>MixedActualEnergyBridge.negativeEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ρ
local notation "SignedCap"=>ENNReal.ofReal ((4*Real.pi^2)^(1/2:ℝ))*ENNReal.ofReal
  ((A*ScalarHeatBandEnvelope.constant P.exponent 0)^2*ScalarHeatBandTime.massConstant P.exponent 0*
    (ProfileVariance.lowerConstant*P.lower)⁻¹*Radius^(2*P.exponent))*Neg
local notation "FactorCap"=>ENNReal.ofReal (MixedNativeFrozenFactorPositive.constant P A ρ*
  Radius^(2*P.exponent+4*ρ)*h^((P.exponent-1)/2)*Global)
local notation "VarianceCap"=>ENNReal.ofReal (MixedNativeVarianceGammaTime.constant P A ρ*
  Radius^(2*P.exponent+4*ρ)*h^((P.exponent-1)/2)*Global)
local notation "CurrentCap"=>ENNReal.ofReal (GammaBandConstants.gradient P A ρ*Radius^(2*P.exponent+4*ρ)*
  min 1 ((4*Global)/Radius^2))
local notation "RootCap"=>ENNReal.ofReal (GammaBandConstants.gradient P A ρ*Radius^(2*P.exponent+4*ρ)*
  min 1 ((2*((0-1:ℝ)^2+(Bnext:ℝ)*PastReferenceBracket.energyConstant P κ 0 1 1)*Global)/Radius^2))
local notation "RawCap"=>(6:ℝ≥0∞)*(ENNReal.ofReal Trace*SignedCap+ENNReal.ofReal Higher*FactorCap+
  ENNReal.ofReal Ksum*(CurrentCap+VarianceCap+RootCap+VarianceCap))

include hIJ₀ hIJ₁ hΛ hH hBDG hh hcover hW0 ha hA hholder in
/-- All six actual measurable envelopes integrate to their proved sharp
caps, with ORIGINAL negative input and ORIGINAL global solution energy.
This is the complete outer sum before structural constant absorption. -/
theorem envelope_energy:(∫⁻r in Ioc (0:ℝ) W,Value Bnext r)≤RawCap:=by
  have hs:=MixedNativeSignedBudget.measurable
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
    (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (j:=j) (ρ:=ρ)
    (A:=A) (h:=h) (hL:=hL) (hρ:=hρ.le)
  have hc:=MixedNativeJointDirectBudget.direct_measurable
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
    (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (h:=h) (ha:=ha)
    (j:=j) (ρ:=ρ)
  have hv:=MixedNativeJointSlotEnvelopes.variance_measurable
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
    (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (h:=h) (A:=A)
    (ρ:=ρ) (j:=j)
  have hf:=MixedNativeJointSlotEnvelopes.factor_measurable
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
    (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (h:=h) (A:=A)
    (ρ:=ρ) (j:=j)
  have hr:=MixedNativeJointSlotEnvelopes.root_measurable
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
    (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (A:=A) (ρ:=ρ)
    (j:=j) (Bnext:=Bnext)
  have hS:=MixedNativeSignedBudget.energy
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
    (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (j:=j) (ρ:=ρ)
    (A:=A) (h:=h) (W:=W) (hL:=hL) (hρ:=hρ.le)
  have hF:=MixedNativeJointEnvelopeEnergy.factor_energy
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
    (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (J:=J) (hIJ₀:=hIJ₀)
    (hIJ₁:=hIJ₁) (hΛ:=hΛ) (hH:=hH) (B:=B) (hBDG:=hBDG) (h:=h)
    (W:=W) (hh:=hh) (hcover:=hcover) (j:=j) (ρ:=ρ) (A:=A)
    (hρ0:=(by linarith : -(1/2:ℝ)<ρ)) (hρ1:=hρhalf)
  have hC:=MixedNativeJointDirectBudget.energy
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
    (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (J:=J) (hIJ₀:=hIJ₀)
    (hIJ₁:=hIJ₁) (hΛ:=hΛ) (hH:=hH) (B:=B) (hBDG:=hBDG) (h:=h)
    (W:=W) (hh:=hh) (hcover:=hcover) (j:=j) (hW0:=hW0) (ha:=ha)
    (hA:=hA) (hholder:=hholder) (ρ:=ρ) (A:=A) (hρ0:=(by linarith : -(1/2:ℝ)<ρ)) (hρ1:=hρhalf)
  have hV:=MixedNativeJointEnvelopeEnergy.variance_energy
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
    (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (J:=J) (hIJ₀:=hIJ₀)
    (hIJ₁:=hIJ₁) (hΛ:=hΛ) (hH:=hH) (B:=B) (hBDG:=hBDG) (h:=h)
    (W:=W) (hh:=hh) (hcover:=hcover) (j:=j) (ρ:=ρ) (A:=A)
    (hρ0:=(by linarith : -(1/2:ℝ)<ρ)) (hρ1:=hρhalf)
  have hR:=MixedNativeJointEnvelopeEnergy.root_energy
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
    (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (J:=J) (hIJ₀:=hIJ₀)
    (hIJ₁:=hIJ₁) (hΛ:=hΛ) (hH:=hH) (B:=B) (hBDG:=hBDG) (h:=h)
    (W:=W) (hh:=hh) (hcover:=hcover) (j:=j) (hW0:=hW0) (hκP:=hκP)
    (Bnext:=Bnext) (ρ:=ρ) (A:=A) (hρ0:=(by linarith : -(1/2:ℝ)<ρ)) (hρ1:=hρhalf)
  exact GammaEnvelopeIntegral.bound (volume.restrict (Ioc (0:ℝ) W))
    Signed FactorEnvelope Direct Variance (Root Bnext) hs hf hc hv hr
    (ENNReal.ofReal Trace) (ENNReal.ofReal Higher) (ENNReal.ofReal Ksum)
    SignedCap FactorCap CurrentCap VarianceCap RootCap hS hF hC hV hR

include hIJ₀ hIJ₁ hΛ hBDG hsmall hBDGpast hhP hBDGγ hlocal hBDGnext in
/-- COMPLETE original physical moving-past Gamma bound with all six
sharp caps attached. No analytic Gamma input is assumed. -/
theorem complete_energy:(∫⁻r in Ioc (0:ℝ) W,Energy r)≤RawCap:=by
  have hE:=MixedNativeJointGammaOuter.complete_energy
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
    (I₁:=I₁) (u₀:=u₀) (S:=S) (J:=J) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁)
    (hΛ:=hΛ) (hH:=hH) (P:=P) (hκP:=hκP) (h:=h) (W:=W)
    (hh:=hh) (hhP:=hhP) (hW0:=hW0) (hcover:=hcover) (hsmall:=hsmall) (Bpast:=Bpast)
    (hBDGpast:=hBDGpast) (hL:=hL) (ha:=ha) (hA:=hA) (hρ:=hρ) (hρhalf:=hρhalf)
    (hholder:=hholder) (j:=j) (hnull:=hnull) (B0:=B0) (B1:=B1) (hBDG0:=hBDG0)
    (hBDG1:=hBDG1) (Bγ:=Bγ) (hBDGγ:=hBDGγ) (hlocal:=hlocal) (Bnext:=Bnext) (hBDGnext:=hBDGnext)
  exact hE.trans (envelope_energy
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
    (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (J:=J) (hIJ₀:=hIJ₀)
    (hIJ₁:=hIJ₁) (hΛ:=hΛ) (hH:=hH) (hκP:=hκP) (h:=h) (W:=W)
    (hh:=hh) (hW0:=hW0) (hcover:=hcover) (hL:=hL) (ha:=ha) (hA:=hA)
    (hρ:=hρ) (hρhalf:=hρhalf) (hholder:=hholder) (j:=j) (Bnext:=Bnext) (B:=B)
    (hBDG:=hBDG))
end SHE.MixedNativeJointGammaIntegral
