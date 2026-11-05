module
public import SHE.MixedNativeEnvelopeUniform
public import SHE.MixedNativeEnvelopeIntegral
public import SHE.MixedNativeFourClockEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false
namespace SHE.MixedNativeMovingEnvelopeRate
open Set MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance mixedNativeMovingEnvelopeRate_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedNativeMovingEnvelopeRate_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance mixedNativeMovingEnvelopeRate_instance3 : MeasurableSpace RealL2 := borel _
local instance mixedNativeMovingEnvelopeRate_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeMovingEnvelopeRate_instance5 : MeasurableSpace CircleL2 := borel _
local instance mixedNativeMovingEnvelopeRate_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedNativeMovingEnvelopeRate_instance7 : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeMovingEnvelopeRate_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeMovingEnvelopeRate_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeMovingEnvelopeRate_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance mixedNativeMovingEnvelopeRate_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance mixedNativeMovingEnvelopeRate_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local notation "Fcur"=>MixedMovingEnergy.ennEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Fneg"=>MixedNativeInputEnergyClock.ennEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Global"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Neg"=>MixedActualEnergyBridge.negativeEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (D:SmoothApproximation.ScalarData){T:ℝ}(hT:0<T)(hT1:T≤1)
    (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2)
local notation "Pzero"=>ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall 0
local notation "scoreFloor"=>ControlledOldIntervals.fraction Pzero*(Pzero).lower
local notation "Cs"=>PhysicalScoreChain.uniformConstant 1
variable (k:ℕ)(hk:0<k)
variable (ρ χ η ε tail ζ:ℝ)(hρ:0<ρ)(hχ0:0≤χ)(hχ1:χ<1)(hm:χ<D.beta+2*ρ)
    (hα:0<ρ+η)(hαhalf:ρ+η<1/2)(hζ:0<ζ)
local notation "Smooth"=>ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall
local notation "Cc"=>NativeCanonicalFrequency.currentCoefficient D hT hT1 hsmall scoreFloor Cs k hk ρ χ hρ hχ0 hχ1 hm ζ hζ
local notation "Cp"=>NativeCanonicalFrequency.pastCoefficient D hT hT1 hsmall scoreFloor Cs k hk ρ χ hρ hχ0 hχ1 hm ζ hζ
local notation "Ci"=>NativeCanonicalFrequency.initialCoefficient D hT hT1 hsmall scoreFloor Cs k hk ρ χ hρ hχ0 hχ1 hm ζ hζ
local notation "Cg"=>NativeCanonicalFrequency.goodCoefficient D hT hT1 hsmall scoreFloor Cs k hk ρ η ε tail ζ hα hαhalf hζ
local notation "Cb"=>NativeCanonicalFrequency.badCoefficient D hT hT1 hsmall scoreFloor Cs k hk ρ η ε tail ζ hα hαhalf hζ
local notation "qc"=>NativeBandFrequencyRates.currentDegree D.beta ρ χ ζ
local notation "qp"=>NativeBandFrequencyRates.pastDegree D.beta ζ
local notation "qg"=>SignedNativeBandFrequency.goodDegree D.beta ε ζ
local notation "qb"=>SignedNativeBandFrequency.badDegree D.beta tail ζ


local notation "Env"=>MovingNativeFourTermEnergy.envelope 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

include hIJ₀ hIJ₁ hχ0 hχ1 hm hα hαhalf hζ in
/-- Frequency decay of the LITERAL complete moving cap, with constants
fixed before every companion n. Both current displacements and the
signed original negative-input clock remain actual model quantities. -/
theorem completed (hΛ:1≤Λ)(hρhalf:ρ<1/2)(hH:(H:ℝ)≤1)
    (B:ℝ≥0)(hBDG:StandardTerminalBDGPower 1 J B)(n:ℕ)(ν:ℝ)(hν:1≤ν)
    (A:ℝ)(p:ℕ)(Bcur Bword:ℝ≥0):
    let h:=NativeBandFrequencyRates.window D.beta ν
    let Cf:=NativeUniversalConstants.rowConstant (1+k)
    let Cdim:=NativeUniversalConstants.currentConstant.{0} (1+k) (by omega)
    let C:=MixedPastNativeQuarterRMS.coefficient κ (M:=M) Pzero k Cf ρ
    let Ccur:=Real.sqrt (8*C*MixedPastNativeEnergyNormalization.currentCoefficient κ (M:=M) Pzero k p χ Cdim Bcur)
    let Cpast:=Real.sqrt (2*C*MixedPastNativeEnergyNormalization.pastCoefficient κ (M:=M) Pzero k Bword)
    let Jt:=MixedPastSignedEndpointMoments.traceConstant (Ω:=Ω) (M:=M) hell ρ hρ hρhalf
    let Cmom:=MixedPastWordMoments.momentConstant Pzero k k p
      ((k:ℝ)*(NativeHybridMoments.momentConstant (p*(k+2)) Bcur κ M)^(Pzero).exponent)
    let Cgood:=PastSignedEndpointTime.goodCoefficient Pzero k Jt ρ η
    let Cbad:=PastSignedEndpointTime.badCoefficient Pzero k M Cmom
    (∫⁻v in Ioc (0:ℝ) ((H:ℝ)-h),∫⁻s in Ioc (0:ℝ) h,
      ENNReal.ofReal (Env (Smooth n) v.toNNReal h.toNNReal s.toNNReal k (A*ν^(-D.beta)) ν Λ ρ χ ν ε tail η hΛ hρ hρhalf p Bcur Bword))≤
    ENNReal.ofReal (8*A^2*Ccur^2)*ENNReal.ofReal (Cc*ν^(-qc))*
      (ENNReal.ofReal Global^χ*(ENNReal.ofReal (H:ℝ))^(1-χ))+
    ENNReal.ofReal (8*A^2*Cpast^2)*ENNReal.ofReal (Cp*ν^(-qp))*ENNReal.ofReal Global+
    ENNReal.ofReal (4*A^2*Cgood^2)*ENNReal.ofReal (Cg*ν^(-qg))*Neg ρ+
    ENNReal.ofReal (4*A^2*Cbad^2)*ENNReal.ofReal (Cb*ν^(-qb))*ENNReal.ofReal (H:ℝ):=by
  intro h Cf Cdim C Ccur Cpast Jt Cmom Cgood Cbad
  have he:=MixedNativeEnvelopeIntegral.completed
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S Pzero
    k A ν ρ χ ε tail η hν hΛ hρ hρhalf hχ0 p Bcur Bword
  have hc:=MixedNativeFourClockEnergy.completed
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    D hT hT1 hsmall scoreFloor Cs k hk ρ χ η ε tail ζ hρ hχ0 hχ1 hm hα hαhalf hζ
    hΛ hH B hBDG 0 ν hν A Ccur Cpast Cgood Cbad
  have hh:=he.trans_le hc
  have hsame:
      (∫⁻v in Ioc (0:ℝ) ((H:ℝ)-h),∫⁻s in Ioc (0:ℝ) h,
        ENNReal.ofReal (Env (Smooth n) v.toNNReal h.toNNReal s.toNNReal k (A*ν^(-D.beta)) ν Λ ρ χ ν ε tail η hΛ hρ hρhalf p Bcur Bword))=
      (∫⁻v in Ioc (0:ℝ) ((H:ℝ)-h),∫⁻s in Ioc (0:ℝ) h,
        ENNReal.ofReal (Env Pzero v.toNNReal h.toNNReal s.toNNReal k (A*ν^(-D.beta)) ν Λ ρ χ ν ε tail η hΛ hρ hρhalf p Bcur Bword)):=by
    apply lintegral_congr_ae
    filter_upwards [] with v
    apply lintegral_congr_ae
    filter_upwards [] with s
    rw [MixedNativeEnvelopeUniform.smooth 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D hT hT1 hsmall n,
      MixedNativeEnvelopeUniform.smooth 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D hT hT1 hsmall 0]
  exact hsame.trans_le hh

end SHE.MixedNativeMovingEnvelopeRate
