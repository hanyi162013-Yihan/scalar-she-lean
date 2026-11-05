module

public import SHE.MovingOriginalGammaHilbert
public import SHE.MixedNativeJointGammaSharpEnergy
public import SHE.MixedNativeJointRowBudgets
public import SHE.MixedNativeJointGammaIntegral
public import SHE.GammaENNRealCollapse
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
namespace SHE.MovingOriginalGammaSharp
open Set MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance mixedNativeMovingCurrentGamma_realSigma : MeasurableSpace RealL2:=borel _
local instance mixedNativeMovingCurrentGamma_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance movingOriginalGammaSharp_nativeSigma : MeasurableSpace CircleL2:=borel _
local instance movingOriginalGammaSharp_nativeBorel : BorelSpace CircleL2:=⟨rfl⟩
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

local notation "OriginalInput"=>MovingOriginalGammaVersion.input
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hκP W h hW0 hh hcover hH hΛ
  hnull B0 B1 hBDG0 hBDG1 ha hA hholder j
local notation "OriginalOutput"=>MovingOriginalGammaHilbert.output
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hκP W h hW0 hh hcover hH
  hnull B0 B1 hBDG0 hBDG1 ha hA hholder j hL hρ hρhalf
local notation "Cgamma"=>JointGammaConstants.constant P A κ Lower Upper LowerPos hρ hρhalf Bnext
variable (hF:StandardItoStoppedParameterFubini J)

include hIJ₀ hIJ₁ hΛ hBDG hsmall hBDGpast hhP hBDGγ hlocal hBDGnext hF in
/-- COMPLETE sharp bound for ONE jointly Borel moving-past native
Hilbert Gamma field, with original SAME-J spatial sections and exact
original I0/I1 physical output sections. The six-slot estimate is
transferred to the TRUE past/sample product; no measurability of an
arbitrarily selected fixed-past reference version is assumed. -/
theorem exists_sharp_output:
    ∃(Y:(ℝ×HeatCircle)×Ω→ℝ)(G:ℝ×Ω→CircleL2),Measurable Y ∧ Measurable G ∧
      (∀ᵐr∂volume.restrict (Ioc (0:ℝ) W),∀ᵐx:HeatCircle∂AddCircle.haarAddCircle,
        (fun ω=>Y ((r,x),ω))=ᵐ[μ] J.integral (OriginalInput r x)) ∧
      (∀ᵐr∂volume.restrict (Ioc (0:ℝ) W),(fun ω=>G (r,ω))=ᵐ[μ] OriginalOutput r) ∧
      (∫⁻z,ENNReal.ofReal (‖G z‖^2) ∂(volume.restrict (Ioc (0:ℝ) W)).prod μ)≤
        ENNReal.ofReal (Cgamma*(Radius^(2*P.exponent)*(Neg).toReal+
          Radius^(2*P.exponent+4*ρ)*(h^((P.exponent-1)/2)*Global+min 1 (Global/Radius^2)))):=by
  let ν:Measure ℝ:=volume.restrict (Ioc (0:ℝ) W)
  haveI:IsFiniteMeasure ν:=by dsimp only [ν];infer_instance
  obtain ⟨Y,G,hY,hG,hYa,hGa,hYf,hFourier⟩:=MovingOriginalGammaHilbert.exists_output
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hκP W h hW0 hh hcover hH hΛ
    hnull B0 B1 hBDG0 hBDG1 ha hA hholder j hL hρ hρhalf J hF hIJ₀ hIJ₁ ν
  refine ⟨Y,G,hY,hG,hYa,hGa,?_⟩
  have he:(∫⁻z,ENNReal.ofReal (‖G z‖^2) ∂ν.prod μ)=∫⁻r in Ioc (0:ℝ) W,Energy r:=by
    rw [lintegral_prod _ ((hG.norm.pow_const 2).ennreal_ofReal).aemeasurable]
    apply lintegral_congr_ae
    filter_upwards [hGa] with r hr
    apply lintegral_congr_ae
    filter_upwards [hr] with ω hω
    rw [hω]
    rfl
  rw [he]
  exact MixedNativeJointGammaSharpEnergy.complete_energy
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV)
    (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S)
    (J:=J) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (hΛ:=hΛ) (hH:=hH) (B:=B) (hBDG:=hBDG)
    (P:=P) (hκP:=hκP) (h:=h) (W:=W) (hh:=hh) (hhP:=hhP) (hW0:=hW0) (hcover:=hcover)
    (hsmall:=hsmall) (Bpast:=Bpast) (hBDGpast:=hBDGpast) (hL:=hL) (ha:=ha) (hA:=hA)
    (hρ:=hρ) (hρhalf:=hρhalf) (hholder:=hholder) (j:=j) (hnull:=hnull)
    (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1) (Bγ:=Bγ) (hBDGγ:=hBDGγ)
    (hlocal:=hlocal) (Bnext:=Bnext) (hBDGnext:=hBDGnext)
end SHE.MovingOriginalGammaSharp

