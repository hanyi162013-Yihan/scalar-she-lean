module

public import SHE.BareGaussianTerminalLeafClockEnergy
public import SHE.HilbertDyadicRemainder
public import SHE.FullLeafClockIdentity
public import SHE.CanonicalGaussianRootBands
public import SHE.FullRemainderConstants
public import SHE.HighFiniteRemainderWeight
public import SHE.BareGaussianRemainderDegree
public import SHE.HilbertDyadicRemainder
public import SHE.MixedNativeFullLeafHilbert
public import SHE.NativeBesselSectionEnergy
public import SHE.InitialOutputExtension
public import SHE.InitialCompleteTimePatch
public import SHE.InitialRetainedFrequencyEnergy
public import SHE.RetainedTerminalAllFrequency
public import SHE.PairedBudgetFrequency
public import SHE.FrequencyTimeInflation
public import SHE.InitialNativeSpatialFields
public import SHE.InitialRetainedSectionEnergy
public import SHE.InitialNativeClock
public import SHE.InitialActualConvolution
public import SHE.MixedTerminalEnergySplit
public import SHE.InitialActualRMSEnvelope
public import SHE.InitialRMSGapEnvelope
public import SHE.InitialTerminalFibre
public import SHE.ZeroDirectionProfile
public import SHE.MixedNativePairInitial
public import SHE.ControlledScalarReference
public import SHE.RelativePairedCurrent
public import SHE.PairedFamilyFields
public import SHE.MovingNativeFields
public import SHE.ShiftedHistoryMeasure
public import SHE.MixedPairedMovingSection
public import SHE.MixedMovingEnergy
public import SHE.ControlledPairedTimeTranslation
public import SHE.MixedPairedClockIntegrals
public import SHE.MixedPastTerminalPairedHistoryEnergy
public import SHE.MixedPastTerminalPairedLinearEnergy
public import SHE.MixedPairedCurrentClock
public import SHE.MixedPastTerminalTimeFields
public import SHE.ControlledTerminalRMSMass
public import SHE.MovingPastFractional
public import SHE.MeanCurrentFields
public import SHE.ControlledMeans
public import SHE.TimeMeasureMass

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.BareGaussianTerminalLeafPrefixes
open Classical
open Set MeasureTheory Real PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance fullNativeRemainderEnergy_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance fullNativeRemainderEnergy_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance fullNativeRemainderEnergy_instance3 : MeasurableSpace RealL2 := borel _
local instance fullNativeRemainderEnergy_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance fullNativeRemainderEnergy_instance5 : MeasurableSpace CircleL2 := borel _
local instance fullNativeRemainderEnergy_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance fullNativeRemainderEnergy_instance7 : MeasurableSpace RealHaarInput := borel _
local instance fullNativeRemainderEnergy_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance fullNativeRemainderEnergy_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance fullNativeRemainderEnergy_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance fullNativeRemainderEnergy_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance fullNativeRemainderEnergy_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)



local instance : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
open SmoothCylinders UniformSmooth
variable(P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable {a:ℝ→ℝ}(ha:BoundedSmooth a){B Hr:ℝ}(hB:∀z,|a z|≤B)(hHr:0≤Hr)
variable(hholder:∀z w,|a z-a w|≤Hr*|z-w|^P.exponent)
variable(hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)
local notation "FF"=>BareGaussianTerminalLeafEnergy.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP ha hL hρ
variable(J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable(hIJ0:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable(hIJ1:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
local notation "Global"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

include hIJ0 hIJ1 hB hHr hholder in
/-- Actual finite native terminal-leaf prefixes, all on the original
output-time/sample measure, retain R^-8 energy with no cutoff-count loss. -/
theorem energy
    (hlocal:StandardTerminalPastLocality J)(hH:(H:ℝ)≤1)
    (hsmallP:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k:ℕ)(hdepth:SHE.depth P.exponent≤k+1)(J0:ℕ)
    (hJH:RemainderBandSpans.span P.exponent (J0+1)≤H)
    (hJP:(RemainderBandSpans.span P.exponent (J0+1):ℝ)≤P.horizon)
    (hJS:∀l,l<k+1→(RemainderBandSpans.span P.exponent (J0+1):ℝ)≤PhysicalScoreChain.uniformHorizon 1 l)
    {χ η:ℝ}(hχ:0<χ)(hχβ:χ<P.exponent)(hχeq:χ=P.exponent/2)
    (hη:0<η)(hηβ:η≤P.exponent/4)(hb:P.exponent≤4/25)
    (order:ℕ)(horder:0<order)(ho0:1≤(order:ℝ)*(1-χ))(ho1:1≤(order:ℝ)*(1-χ/P.exponent))
    (B0 B1 Bcov:ℝ≥0)(hBDG:StandardTerminalBDGPower (order*((k+1)+2)) J B0)
    (hBDG1:StandardTerminalBDGPower 1 J B1)(hBDGcov:StandardTerminalBDGPower (k+3) J Bcov):
    let C:=FullRemainderConstants.comparison P κ M (H:ℝ) (k+1) χ η order B0 B1 Bcov
    let A:=ScalarHeatBandBernstein.amplitude B Hr P.exponent (k+2)
    let D:=Λ^(-ρ)*C*A^2*(2:ℝ)^(2*(P.exponent/2+η))*Global^χ
    ∀L:ℕ,Integrable (fun z=>‖∑j∈Finset.range L,FF k (J0+j) z‖^2) (energyMeasure μ H) ∧
      (∫z,‖∑j∈Finset.range L,FF k (J0+j) z‖^2 ∂energyMeasure μ H)≤
        D*(256/225:ℝ)*((2:ℝ)^(J0+1))^(-8:ℝ):=by
  intro C A D
  have hC:0≤C:=by
    unfold C FullRemainderConstants.comparison
    have hc:=MixedPastWordMoments.momentConstant_nonneg P (k+1) (k+1) 1
      (((k+1:ℕ):ℝ)*(NativeHybridMoments.momentConstant (k+3) Bcov κ M)^P.exponent)
    positivity
  have hGlobal:=MixedMovingEnergy.globalEnergy_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  have hD:0≤D:=by dsimp only [D];positivity
  let F:ℕ→(ℝ≥0×Ω)→CircleL2:=fun j=>FF k (J0+j)
  have hFm(j:ℕ):Measurable (F j):=BareGaussianTerminalLeafEnergy.field_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP ha hL hρ k (J0+j)
  have he(j:ℕ):Integrable (fun z=>‖F j z‖^2) (energyMeasure μ H) ∧
      (∫z,‖F j z‖^2 ∂energyMeasure μ H)≤D*((2:ℝ)^(J0+1+j))^(-8:ℝ):=by
    have hspan:RemainderBandSpans.span P.exponent (J0+j+1)≤RemainderBandSpans.span P.exponent (J0+1):=
      RemainderBandSpans.span_antitone P.exponent_pos.le (by omega)
    have hsR:(RemainderBandSpans.span P.exponent (J0+j+1):ℝ)≤
        (RemainderBandSpans.span P.exponent (J0+1):ℝ):=hspan
    have hh:=BareGaussianTerminalLeafClockEnergy.energy
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP ha hB hHr hholder hL hρ J hIJ0 hIJ1
      hlocal hH hsmallP k (J0+j) hdepth (hspan.trans hJH) (hsR.trans hJP)
      (fun l hl=>hsR.trans (hJS l hl)) hχ hχβ hχeq hη hηβ hb
      order horder ho0 ho1 B0 B1 Bcov hBDG hBDG1 hBDGcov
    simpa only [show J0+j+1=J0+1+j by omega] using hh
  intro L
  exact HilbertDyadicRemainder.finite_energy (energyMeasure μ H) F hFm (fun j=>(he j).1)
    (J0+1) L hD (fun j=>(he j).2)
end SHE.BareGaussianTerminalLeafPrefixes
