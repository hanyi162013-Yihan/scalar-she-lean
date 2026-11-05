module

public import SHE.MixedNativeJointRowBudgets
public import SHE.MixedNativeJointSlotEnvelopes
public import SHE.MixedNativeMovingJointBudgets
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
namespace SHE.MixedNativeJointEnvelopeEnergy
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

local notation "Variance"=>MixedNativeJointSlotEnvelopes.variance 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P h
local notation "FactorEnvelope"=>MixedNativeJointSlotEnvelopes.factor 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P h
local notation "Root"=>MixedNativeJointSlotEnvelopes.root 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P

include hIJ₀ hIJ₁ hΛ hH hBDG hh hcover in
/-- Integrate the actual measurable variance envelope using TRUE past
solution energy; no reference-version interchange is assumed. -/
theorem variance_energy {A ρ:ℝ} (hρ0:-(1/2:ℝ)<ρ) (hρ1:ρ<1/2) (j:ℕ):
    (∫⁻r in Ioc (0:ℝ) W,Variance A ρ j r)≤ENNReal.ofReal
      (MixedNativeVarianceGammaTime.constant P A ρ*CompactMollifier.radius (j+1)^(2*P.exponent+4*ρ)*h^((P.exponent-1)/2)*Global):=by
  have hW:W≤H:=by linarith
  have hC:0≤MixedNativeVarianceGammaTime.constant P A ρ*CompactMollifier.radius (j+1)^(2*P.exponent+4*ρ)*h^((P.exponent-1)/2):=by
    have hc:=GammaBandConstants.variance_nonneg P A hρ0 hρ1
    have hr:=CompactMollifier.radius_pos (j+1)
    positivity
  exact MixedNativePastBudget.linear 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ hH B hBDG hW hC
    (Variance A ρ j) (fun _ _=>le_rfl)

include hIJ₀ hIJ₁ hΛ hH hBDG hh hcover in
/-- Actual frozen-factor dominating envelope with the sharp two-face
frequency gain and the original global path mass. -/
theorem factor_energy {A ρ:ℝ} (hρ0:-(1/2:ℝ)<ρ) (hρ1:ρ<1/2) (j:ℕ):
    (∫⁻r in Ioc (0:ℝ) W,FactorEnvelope A ρ j r)≤ENNReal.ofReal
      (MixedNativeFrozenFactorPositive.constant P A ρ*CompactMollifier.radius (j+1)^(2*P.exponent+4*ρ)*h^((P.exponent-1)/2)*Global):=by
  have hW:W≤H:=by linarith
  have hC:0≤MixedNativeFrozenFactorPositive.constant P A ρ*CompactMollifier.radius (j+1)^(2*P.exponent+4*ρ)*h^((P.exponent-1)/2):=by
    have hc:=GammaBandConstants.frozen_factor_nonneg P A hρ0 hρ1
    have hr:=CompactMollifier.radius_pos (j+1)
    change 0≤MixedNativeFrozenFactorGammaTime.constant P A ρ*CompactMollifier.radius (j+1)^(2*P.exponent+4*ρ)*h^((P.exponent-1)/2)
    positivity
  exact MixedNativePastBudget.linear 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ hH B hBDG hW hC
    (FactorEnvelope A ρ j) (fun _ _=>le_rfl)

include hIJ₀ hIJ₁ hΛ hH hBDG hh hW0 hcover hκP in
/-- Compatible frozen-root clipping is performed AFTER true past
averaging, with no jointly chosen family of reference modifications. -/
theorem root_energy {A ρ:ℝ} (hρ0:-(1/2:ℝ)<ρ) (hρ1:ρ<1/2) (j:ℕ)(Bnext:ℝ≥0):
    (∫⁻r in Ioc (0:ℝ) W,Root A ρ j Bnext r)≤ENNReal.ofReal
      (GammaBandConstants.gradient P A ρ*CompactMollifier.radius (j+1)^(2*P.exponent+4*ρ)*
        min 1 ((2*((0-1:ℝ)^2+(Bnext:ℝ)*PastReferenceBracket.energyConstant P κ 0 1 1)*Global)/CompactMollifier.radius (j+1)^2)):=by
  have hW:W≤H:=by linarith
  have hC:0≤GammaBandConstants.gradient P A ρ*CompactMollifier.radius (j+1)^(2*P.exponent+4*ρ):=by
    have hc:=GammaBandConstants.gradient_nonneg P A hρ0 hρ1
    have hr:=CompactMollifier.radius_pos (j+1)
    positivity
  exact MixedNativePastBudget.clipped 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ hH B hBDG
    hW0 hW hC (GammaBandConstants.reference_clip_nonneg P hκP Bnext) (CompactMollifier.radius_pos (j+1))
      (Root A ρ j Bnext) (fun _ _=>le_rfl)
end SHE.MixedNativeJointEnvelopeEnergy
