module

public import SHE.CanonicalGaussianTerminalLeafPrefixes
public import SHE.CanonicalGaussianRootBands
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

namespace SHE.CanonicalGaussianTerminalLeafRMS
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
open SmoothCylinders SmoothApproximation
variable(P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable(D:ScalarData){tau:ℝ}(htau:0<tau)(htau1:tau≤1)
variable(hcontract:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*tau^(D.beta/4)≤1/2)
variable(n:ℕ)(hP:P=ControlledSmoothLimit.smoothTotalParameters D htau htau1 hcontract n)
variable(hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)
local notation "FF"=>BareGaussianTerminalLeafEnergy.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
  (D.smooth_boundedSmooth n) hL hρ
variable(J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable(hIJ0:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable(hIJ1:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
local notation "Global"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Rough"=>ControlledSmoothLimit.roughTotalParameters D htau htau1 hcontract

include hP hIJ0 hIJ1 in
theorem rms
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
    let C:=FullRemainderConstants.comparison Rough κ M (H:ℝ) (k+1) χ η order B0 B1 Bcov
    let A:=CanonicalGaussianRootBands.amplitude D 1 (k+2)
    ∀L:ℕ,Integrable (fun z=>‖∑j∈Finset.range L,FF k (J0+j) z‖^2) (energyMeasure μ H) ∧
      Real.sqrt (∫z,‖∑j∈Finset.range L,FF k (J0+j) z‖^2 ∂energyMeasure μ H)≤
        Λ^(-ρ/2)*Real.sqrt C*A*(2:ℝ)^(D.beta/2+η)*(16/15:ℝ)*
          ((2:ℝ)^(J0+1))^(-4:ℝ)*Global^(χ/2) :=by
  intro C A
  have he:=CanonicalGaussianTerminalLeafPrefixes.energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP D htau htau1 hcontract n hP hL hρ J hIJ0 hIJ1
    hlocal hH hsmallP k hdepth J0 hJH hJP hJS hχ hχβ hχeq hη hηβ hb
    order horder ho0 ho1 B0 B1 Bcov hBDG hBDG1 hBDGcov
  have hC:0≤C:=by
    unfold C FullRemainderConstants.comparison
    have hc:=MixedPastWordMoments.momentConstant_nonneg Rough (k+1) (k+1) 1
      (((k+1:ℕ):ℝ)*(NativeHybridMoments.momentConstant (k+3) Bcov κ M)^(Rough).exponent)
    positivity
  have hA:0≤A:=CanonicalGaussianRootBands.amplitude_nonneg D zero_le_one (k+2)
  have hΛ:0≤Λ:=zero_le_one.trans hL
  have hGlobal:=MixedMovingEnergy.globalEnergy_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  let R:ℝ:=(2:ℝ)^(J0+1)
  let T:=Λ^(-ρ/2)*Real.sqrt C*A*(2:ℝ)^(D.beta/2+η)*(16/15:ℝ)*R^(-4:ℝ)*Global^(χ/2)
  have hT:0≤T:=by dsimp only [T,R];positivity
  have hsq:T^2=(Λ^(-ρ)*C*A^2*(2:ℝ)^(2*(D.beta/2+η))*Global^χ)*
      (256/225:ℝ)*R^(-8:ℝ):=by
    have h1:(Λ^(-ρ/2))^2=Λ^(-ρ):=by
      rw [←Real.rpow_mul_natCast hΛ]
      congr 1
      norm_num <;> ring
    have h2:((2:ℝ)^(D.beta/2+η))^2=(2:ℝ)^(2*(D.beta/2+η)):=by
      rw [←Real.rpow_mul_natCast (by norm_num:(0:ℝ)≤2)]
      congr 1
      norm_num <;> ring
    have h3:(R^(-4:ℝ))^2=R^(-8:ℝ):=by
      rw [←Real.rpow_mul_natCast (show 0≤R by dsimp [R];positivity)]
      norm_num
    have h4:(Global^(χ/2))^2=Global^χ:=by
      rw [←Real.rpow_mul_natCast hGlobal]
      congr 1
      norm_num <;> ring
    dsimp only [T]
    simp only [mul_pow,h1,h2,h3,h4,Real.sq_sqrt hC]
    norm_num <;> ring
  intro L
  refine ⟨(he L).1,?_⟩
  change Real.sqrt _≤T
  apply Real.sqrt_le_iff.mpr
  refine ⟨hT,?_⟩
  rw [hsq]
  exact (he L).2
end SHE.CanonicalGaussianTerminalLeafRMS
