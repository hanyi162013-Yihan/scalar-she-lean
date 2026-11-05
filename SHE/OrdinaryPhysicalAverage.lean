module
public import SHE.OrdinaryLevelPhysicalInput
public import SHE.OrdinaryGradientBounds
public import SHE.TerminalItoRawAverage

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.OrdinaryPhysicalAverage
open Set MeasureTheory PredictableL2 FiniteHaar DyadicApproximation StoppedFourier
  NativeHeatObservation WordRecursion OrthogonalItoChannels CutoffWordLevel
open scoped NNReal ENNReal
local instance ordinaryPhysicalAverage_realSigma:MeasurableSpace RealL2:=borel _
local instance ordinaryPhysicalAverage_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance ordinaryPhysicalAverage_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance ordinaryPhysicalAverage_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
local instance ordinaryPhysicalAverage_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance ordinaryPhysicalAverage_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance ordinaryPhysicalAverage_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance ordinaryPhysicalAverage_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω Y:Type}[MeasurableSpace Ω][MeasurableSpace Y]
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[IsProbabilityMeasure μ]
variable {H:ℝ≥0}{κ:ℝ}{a:ℝ→ℝ}{ell M:ℝ}(m:TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)
variable {R:ReferenceData}{n:ℕ}(L:Level R Y n)

/-- Genuine finite old-history averaging of the ordinary-U physical
input preserves its original J representation and literal raw row. -/
theorem original_input (hh:R.horizon≤(H:ℝ)){η:ℝ}(hη:0<η)
    (hgap:∀p i,η≤(L.observations.observations p i).target-L.terminal p)
    (ν:Measure Y)[IsFiniteMeasure ν]:
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      input=ᵐ[energyMeasure μ H] (fun z=>∫p,OrdinaryPhysicalGradient.raw m L (p,z) ∂ν)∧
      m.scalarIto.integral input=ᵐ[μ] fun ω=>∫p,OrdinaryUncutNoise.version m L p ω ∂ν:=by
  obtain ⟨D,hD,hDb⟩:=OrdinaryGradientBounds.raw_bound m L hη hgap
  obtain ⟨B,hB,hBb⟩:=OrdinaryUncutNoise.version_bound m L
  exact TerminalItoRawAverage.bounded_average 𝓕 μ H m.scalarIto ν
    (OrdinaryPhysicalGradient.raw m L) (OrdinaryPhysicalGradient.raw_predictable m L)
    hD (fun p z=>hDb (p,z))
    (fun z:Y×Ω=>OrdinaryUncutNoise.version m L z.1 z.2) (OrdinaryUncutNoise.version_measurable m L)
    hB hBb (fun p=>OrdinaryLevelPhysicalInput.original_section_input m L hh hη hgap p)

end SHE.OrdinaryPhysicalAverage
