module
public import SHE.MovingNativeFourTermEnergy
public import SHE.NativeNormalizedConstantUniform
public import SHE.SignedNativeConstantUniform
public import SHE.NativeCanonicalFrequency

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.MixedNativeEnvelopeUniform
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation Real
  ControlledProfile ControlledReferenceLevel ControlledOldIntervals NativeSignedHaarProcess PhysicalScoreChain
  SmoothCylinders UniformSmooth CutoffWordLevel
open scoped NNReal ENNReal
local instance mixedNativeEnvelopeUniform_realSigma:MeasurableSpace RealL2:=borel _
local instance mixedNativeEnvelopeUniform_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance mixedNativeEnvelopeUniform_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance mixedNativeEnvelopeUniform_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
local instance mixedNativeEnvelopeUniform_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance mixedNativeEnvelopeUniform_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z∧aU z≤M)(hbV:∀z,ell≤aV z∧aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

variable (D:SmoothApproximation.ScalarData){T:ℝ}(hT:0<T)(hT1:T≤1)
    (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2)
local notation "Smooth"=>ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall
local notation "Rough"=>ControlledSmoothLimit.roughTotalParameters D hT hT1 hsmall
local notation "Env"=>MovingNativeFourTermEnergy.envelope 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

/-- The complete physical native envelope is independent of the
companion smoothing index, not merely its scalar frequency exponent. -/
theorem smooth (n:ℕ)(v h s:ℝ≥0)(k:ℕ)(A0 ν mass ρ χ lam ε tail η:ℝ)
    (hmass:1≤mass)(hρ:0<ρ)(hρhalf:ρ<1/2)(p:ℕ)(Bcur Bword:ℝ≥0):
    Env (Smooth n) v h s k A0 ν mass ρ χ lam ε tail η hmass hρ hρhalf p Bcur Bword=
      Env Rough v h s k A0 ν mass ρ χ lam ε tail η hmass hρ hρhalf p Bcur Bword:=by
  dsimp only [MovingNativeFourTermEnergy.envelope]
  simp only [NativeNormalizedConstantUniform.current D hT hT1 hsmall,
    NativeNormalizedConstantUniform.past D hT hT1 hsmall,
    SignedNativeConstantUniform.actual_moment D hT hT1 hsmall,
    NativeCanonicalFrequency.majorant_smooth D hT hT1 hsmall]
  rfl

end SHE.MixedNativeEnvelopeUniform
