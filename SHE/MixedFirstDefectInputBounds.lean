module

public import SHE.MixedFirstDefectInputRMS
public import SHE.MixedActualEnergyBridge
public import SHE.PredictableScalarField
public import SHE.MixedNativeCoefficientField
public import SHE.MixedActualNegativeRMS
public import SHE.MixedFirstDefectRMS
public import SHE.ScalarTimeZeroExtension
public import SHE.TimeTranslationAverage

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.MixedFirstDefectInputBounds
open MeasureTheory AddCircle GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance firstGammaReferenceEnergy_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance firstGammaFrozenValues_realSigma : MeasurableSpace RealL2 := borel _
local instance firstGammaFrozenValues_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance firstGammaFrozenValues_circleSigma : MeasurableSpace CircleL2 := borel _
local instance firstGammaFrozenValues_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance firstGammaFrozenValues_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance firstGammaFrozenValues_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance firstGammaFrozenValues_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance firstGammaFrozenValues_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

variable (hΛ:0≤Λ) (hH:(H:ℝ)≤1)
local notation "hM"=>(hell.le.trans ((hbU 0).1.trans (hbU 0).2))
local notation "fU"=>ContinuousHeatMild.coefficientFunction haU hell hbU S.first
local notation "fV"=>ContinuousHeatMild.coefficientFunction haV hell hbV S.second



local instance actualEnergyBridge_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance actualEnergyBridge_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance actualEnergyBridge_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance actualEnergyBridge_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance actualEnergyBridge_realSecond : SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology


local notation "Input"=>MixedNativeCoefficientField.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Neg"=>MixedActualEnergyBridge.negativeEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

local notation "RMS"=>MixedActualNegativeRMS.rms 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "E"=>MixedFirstDefectRMS.inputEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S


/-- A coarse boundedness check for L1 applicability only. The sharp
quantitative convolution retains the actual negative input unchanged. -/
theorem rms_bound (ρ:ℝ)(hL:1≤Λ)(hρ:0≤ρ)(p:ℝ≥0×Ω):
    0≤RMS ρ hL hρ p ∧ RMS ρ hL hρ p≤|M-ell|:=by
  refine ⟨norm_nonneg _,?_⟩
  have hb:=NativeSignedHaarProcess.inputEnergy_bound hL hρ (fU p) (fV p)
  have hs:=Real.sqrt_le_sqrt hb
  have he:NativeSignedHaarProcess.inputEnergy hL hρ (fU p) (fV p)=E ρ hL hρ (p.1:ℝ) p.2:=by
    simp only [MixedFirstDefectRMS.inputEnergy,Real.toNNReal_coe]
  rw [he,MixedFirstDefectInputRMS.input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S,
    Real.toNNReal_coe,Real.sqrt_sq_eq_abs] at hs
  exact hs

theorem extended_bound (ρ:ℝ)(hL:1≤Λ)(hρ:0≤ρ)(z:ℝ×Ω):
    0≤ScalarTimeZeroExtension.extend H (RMS ρ hL hρ) z ∧
      ScalarTimeZeroExtension.extend H (RMS ρ hL hρ) z≤|M-ell|:=by
  by_cases hz:z.1∈Set.Ioc (0:ℝ) (H:ℝ)
  · simpa only [ScalarTimeZeroExtension.extend,Set.indicator_of_mem hz] using
      rms_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ρ hL hρ (z.1.toNNReal,z.2)
  · simp only [ScalarTimeZeroExtension.extend,Set.indicator_of_notMem hz]
    exact ⟨le_rfl,abs_nonneg _⟩
end SHE.MixedFirstDefectInputBounds
