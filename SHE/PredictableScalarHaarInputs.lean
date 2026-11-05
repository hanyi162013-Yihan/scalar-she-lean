module
public import SHE.PredictableScalarHaarRotation
public import SHE.RotatedFiniteIto
public import SHE.RotatedLevy
public import SHE.RotatedNovikov
public import SHE.ItoLocalityTransport
public import SHE.StandardTerminalBDGPower
public import SHE.RotatedStoppedFubini
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.PredictableScalarHaarRotation
open MeasureTheory CircleHeat FiniteHaar DyadicApproximation AddCircle PredictableL2
open NoiseSplitting OrthogonalItoChannels AdditivePhysicalFactor StoppedFourier
open scoped NNReal ENNReal
local instance scalarHaarInputs_unitPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance scalarHaarInputs_circleSecond : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance scalarHaarInputs_realSecond : SecondCountableTopology RealL2 :=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance scalarHaarInputs_realSigma : MeasurableSpace RealL2 := borel _
local instance scalarHaarInputs_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance scalarHaarInputs_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance scalarHaarInputs_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (D : SmoothApproximation.ScalarData)
variable (U : ℝ≥0 × Ω → RealL2) (hU : StronglyMeasurable[𝓕.predictable] U)
variable (B : StandardTerminalIto (C:=Both RealL2) (E:=ℝ) 𝓕 μ H)

/-- Ordinary finite Ito applies to the actual solution-dependent split noise. -/
theorem finiteIto (hB : StandardFiniteIto.Universal 𝓕 μ H B) :
    StandardFiniteIto.Universal 𝓕 μ H (integral 𝓕 μ H D U hU B) :=
  RotatedFiniteIto.universal 𝓕 μ H (field D U) (field_measurable 𝓕 D U hU) B hB

/-- No additional Brownian recognition input is needed for this rotation. -/
theorem levy (hB : StandardTerminalLevy B) :
    StandardTerminalLevy (integral 𝓕 μ H D U hU B) :=
  PredictableItoRotation.levy 𝓕 μ H (field D U) (field_measurable 𝓕 D U hU) B hB

theorem locality (hB : StandardTerminalPastLocality B) :
    StandardTerminalPastLocality (integral 𝓕 μ H D U hU B) :=
  ItoLocalityTransport.rotation 𝓕 μ H (field D U) (field_measurable 𝓕 D U hU) B hB

/-- The actual rotated input has exactly the original bracket. -/
theorem novikov (hB : StandardTerminalNovikov B) :
    StandardTerminalNovikov (integral 𝓕 μ H D U hU B) :=
  PredictableItoRotation.novikov 𝓕 μ H (field D U) (field_measurable 𝓕 D U hU) B hB

theorem bdgPower (p : ℕ) (K : ℝ≥0) (hB : StandardTerminalBDGPower p B K) :
    StandardTerminalBDGPower p (integral 𝓕 μ H D U hU B) K :=
  PredictableItoRotation.bdgPower 𝓕 μ H (field D U) (field_measurable 𝓕 D U hU) p B K hB

theorem stoppedFubini (hB : StandardItoStoppedParameterFubini B) :
    StandardItoStoppedParameterFubini (integral 𝓕 μ H D U hU B) :=
  PredictableItoRotation.stoppedParameterFubini 𝓕 μ H (field D U)
    (field_measurable 𝓕 D U hU) B hB
end SHE.PredictableScalarHaarRotation
