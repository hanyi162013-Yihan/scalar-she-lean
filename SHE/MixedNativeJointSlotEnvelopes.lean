module

public import SHE.MixedNativeJointRowBudgets
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
namespace SHE.MixedNativeJointSlotEnvelopes
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

def variance (A ρ:ℝ)(j:ℕ)(r:ℝ):ℝ≥0∞:=ENNReal.ofReal
  (MixedNativeVarianceGammaTime.constant P A ρ*CompactMollifier.radius (j+1)^(2*P.exponent+4*ρ)*h^((P.exponent-1)/2)*E r)
def factor (A ρ:ℝ)(j:ℕ)(r:ℝ):ℝ≥0∞:=ENNReal.ofReal
  (MixedNativeFrozenFactorPositive.constant P A ρ*CompactMollifier.radius (j+1)^(2*P.exponent+4*ρ)*h^((P.exponent-1)/2)*E r)
def root (A ρ:ℝ)(j:ℕ)(Bnext:ℝ≥0)(r:ℝ):ℝ≥0∞:=ENNReal.ofReal
  (GammaBandConstants.gradient P A ρ*CompactMollifier.radius (j+1)^(2*P.exponent+4*ρ)*
    min 1 ((2*((0-1:ℝ)^2+(Bnext:ℝ)*PastReferenceBracket.energyConstant P κ 0 1 1)*E r)/CompactMollifier.radius (j+1)^2))
local notation "Variance"=>variance 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P h
local notation "FactorEnvelope"=>factor 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P h
local notation "Root"=>root 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P

/-- The dominating past energy is the TRUE original coupled-pair energy. -/
theorem past_measurable:Measurable (fun r:ℝ=>E r):=
  (MixedMovingEnergy.energy_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S).comp measurable_real_toNNReal

theorem variance_measurable (A ρ:ℝ)(j:ℕ):Measurable (Variance A ρ j):=
  ENNReal.measurable_ofReal.comp ((past_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S).const_mul _)
theorem factor_measurable (A ρ:ℝ)(j:ℕ):Measurable (FactorEnvelope A ρ j):=
  ENNReal.measurable_ofReal.comp ((past_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S).const_mul _)
theorem root_measurable (A ρ:ℝ)(j:ℕ)(Bnext:ℝ≥0):Measurable (Root A ρ j Bnext):=by
  have he:=past_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  exact ENNReal.measurable_ofReal.comp ((measurable_const.min ((he.const_mul _).div_const _)).const_mul _)

include hIJ₀ hIJ₁ hΛ hH hsmall hBDGpast hhP hh hW0 hcover in
theorem current_variance_le {a:ℝ→ℝ} (ha:SmoothCylinders.BoundedSmooth a) {A ρ:ℝ}
    (hA:0≤A) (hρ0:-(1/2:ℝ)<ρ) (hρ1:ρ<1/2)
    (hholder:∀x y,|a x-a y|≤A*|x-y|^P.exponent)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1)
    (j:ℕ)(r:ℝ)(hr:r∈Ioc (0:ℝ) W):Budget a j ρ 1 2 r≤Variance A ρ j r:=by
  have hw:(Terminal r:ℝ)-(Past r:ℝ)≤P.horizon:=by rw [span r];exact hhP
  have he:=MixedNativeJointRowBudgets.current_variance
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S)
    (J:=J) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (P:=P) (hκP:=hκP) (hΛ:=hΛ) (v:=Past r) (b:=Terminal r)
    (hvb:=ordered r) (hbH:=covered r) (hH:=hH) (hwindow:=hw) (hsmall:=hsmall) (Bpast:=Bpast) (hBDGpast:=hBDGpast)
    ha hA hρ0 hρ1 hholder hnull B0 B1 hBDG0 hBDG1 j
  rw [span r] at he
  simpa only [MixedNativeMovingJointBudgets.budget,variance,NativeMovingGammaClock.past_eq hr,MixedMovingEnergy.energy,mul_assoc] using he

include hIJ₀ hIJ₁ hΛ hH hsmall hBDGpast hhP hh hW0 hcover in
theorem reference_variance_le {a:ℝ→ℝ} (ha:SmoothCylinders.BoundedSmooth a) {A ρ:ℝ}
    (hA:0≤A) (hρ0:-(1/2:ℝ)<ρ) (hρ1:ρ<1/2)
    (hholder:∀x y,|a x-a y|≤A*|x-y|^P.exponent)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1)
    (j:ℕ)(r:ℝ)(hr:r∈Ioc (0:ℝ) W):Budget a j ρ 4 5 r≤Variance A ρ j r:=by
  have hw:(Terminal r:ℝ)-(Past r:ℝ)≤P.horizon:=by rw [span r];exact hhP
  have he:=MixedNativeJointRowBudgets.reference_variance
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S)
    (J:=J) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (P:=P) (hκP:=hκP) (hΛ:=hΛ) (v:=Past r) (b:=Terminal r)
    (hvb:=ordered r) (hbH:=covered r) (hH:=hH) (hwindow:=hw) (hsmall:=hsmall) (Bpast:=Bpast) (hBDGpast:=hBDGpast)
    ha hA hρ0 hρ1 hholder hnull B0 B1 hBDG0 hBDG1 j
  rw [span r] at he
  simpa only [MixedNativeMovingJointBudgets.budget,variance,NativeMovingGammaClock.past_eq hr,MixedMovingEnergy.energy,mul_assoc] using he

include hIJ₀ hIJ₁ hΛ hH hsmall hBDGpast hhP hh hW0 hcover in
theorem factor_le {A ρ:ℝ} (hρ0:-(1/2:ℝ)<ρ) (hρ1:ρ<1/2) (j:ℕ)(r:ℝ)(hr:r∈Ioc (0:ℝ) W):
    Factor A ρ j r≤FactorEnvelope A ρ j r:=by
  have hw:(Terminal r:ℝ)-(Past r:ℝ)≤P.horizon:=by rw [span r];exact hhP
  have he:=MixedNativeFrozenFactorPositive.energy
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S)
    (J:=J) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (P:=P) (hκP:=hκP) (hΛ:=hΛ) (v:=Past r) (b:=Terminal r)
    (hvb:=ordered r) (hbH:=covered r) (hH:=hH) (hwindow:=hw) (hsmall:=hsmall) (Bpast:=Bpast) (hBDGpast:=hBDGpast)
    (A:=A) hρ0 hρ1 j
  rw [span r] at he
  simpa only [MixedNativeMovingFrozenFactor.budget,factor,NativeMovingGammaClock.past_eq hr,MixedMovingEnergy.energy,mul_assoc] using he

variable (Bγ:ℝ≥0) (hBDGγ:StandardTerminalBDG16 J Bγ)
include hIJ₀ hIJ₁ hΛ hH hsmall hBDGpast hhP hh hW0 hcover hBDGγ in
theorem root_le {a:ℝ→ℝ} (ha:SmoothCylinders.BoundedSmooth a) {A ρ:ℝ}
    (hA:0≤A) (hρ0:-(1/2:ℝ)<ρ) (hρ1:ρ<1/2)
    (hholder:∀x y,|a x-a y|≤A*|x-y|^P.exponent)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1)
    (hlocal:StandardTerminalPastLocality I₁) (Bnext:ℝ≥0) (hBDGnext:StandardTerminalBDGPower 1 I₁ Bnext)
    (j:ℕ)(r:ℝ)(hr:r∈Ioc (0:ℝ) W):Budget a j ρ 3 4 r≤Root A ρ j Bnext r:=by
  have hw:(Terminal r:ℝ)-(Past r:ℝ)≤P.horizon:=by rw [span r];exact hhP
  have he:=MixedNativeJointRowBudgets.reference_root
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S)
    (J:=J) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (P:=P) (hκP:=hκP) (hΛ:=hΛ) (v:=Past r) (b:=Terminal r)
    (hvb:=ordered r) (hbH:=covered r) (hH:=hH) (hwindow:=hw) (hsmall:=hsmall) (Bpast:=Bpast) (hBDGpast:=hBDGpast)
    (B:=Bγ) (hBDG:=hBDGγ) ha hA hρ0 hρ1 hholder hnull B0 B1 hBDG0 hBDG1 hlocal Bnext hBDGnext j
  simpa only [MixedNativeMovingJointBudgets.budget,root,GammaBandConstants.gradient,NativeMovingGammaClock.past_eq hr,
    MixedMovingEnergy.energy,mul_assoc] using he
end SHE.MixedNativeJointSlotEnvelopes
