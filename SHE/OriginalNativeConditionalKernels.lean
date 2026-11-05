module
public import SHE.OriginalShiftedSingleModels
public import SHE.ConditionalStateProjection
public import SHE.NativePathRestrictionClock
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
namespace SHE.OriginalNativeConditionalKernels
open MeasureTheory ProbabilityTheory Set PredictableL2 FiniteHaar DyadicApproximation OrthogonalItoChannels
open scoped NNReal ENNReal
local instance conditionalKernels_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance conditionalKernels_circleSecond:SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance conditionalKernels_realSecond:SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance conditionalKernels_realSigma:MeasurableSpace RealL2:=borel _
local instance conditionalKernels_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance conditionalKernels_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance conditionalKernels_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance conditionalKernels_bothSigma:MeasurableSpace (Both RealL2):=borel _
local instance conditionalKernels_bothBorel:BorelSpace (Both RealL2):=⟨rfl⟩
variable {Ω:Type*} [MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω) [IsProbabilityMeasure μ] (H:ℝ≥0)
variable (D:SmoothApproximation.ScalarData) (B:StandardTerminalIto (C:=Both RealL2) (E:=ℝ) 𝓕 μ H)
variable (u₀:RealL2) (S:OriginalNativeHeatEquation.Data 𝓕 μ H D B u₀)
variable (v h:ℝ≥0) (hpos:0<H)

def pastPath := NativeContinuousPath.path v S.value S.continuous
def future := NativeContinuousPath.path h (fun t ω=>S.value (v+t) ω)
  (NativePathRestrictionClock.shifted_continuous v S.value S.continuous)
def stateKernel := condDistrib (future 𝓕 μ H D B u₀ S v h) (pastPath 𝓕 μ H D B u₀ S v) μ

/-- The true future STATE kernel is the state projection of the actual
conditional weak model, under the actual state-pastPath law. No equality
of joint state-and-noise pastPath laws is involved. -/
theorem state_projection (C:ℝ≥0) (hBDG:StandardTerminalBDG16 B C)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ) :
    stateKernel 𝓕 μ H D B u₀ S v h=ᵐ[μ.map (pastPath 𝓕 μ H D B u₀ S v)]
      (OriginalShiftedSingleModels.kernel 𝓕 μ H D B u₀ S v h hpos).map Prod.fst := by
  have hp : Measurable (pastPath 𝓕 μ H D B u₀ S v) :=
    NativeContinuousPath.measurable_path v S.value S.continuous
      (S.predictable.mono (predictable_le_product 𝓕)).measurable
  have hUa : ∀t,Measurable[𝓕 t] (S.value t) :=
    fun t=>(show IsStronglyPredictable 𝓕 S.value from S.predictable).stronglyAdapted t |>.measurable
  have hb := OriginalConditionalWhiteNoise.bundle_measurable 𝓕 μ H S.value S.continuous hUa
    (OriginalNativeWhiteDriver.integral 𝓕 μ H B) C (OriginalNativeWhiteDriver.bdg 𝓕 μ H B C hBDG)
    hpos hnull v h
  exact ConditionalStateProjection.state_fst μ (pastPath 𝓕 μ H D B u₀ S v)
    (OriginalShiftedSingleModels.futureBundle 𝓕 μ H D B u₀ S v h hpos)
    hp.aemeasurable hb.aemeasurable
end SHE.OriginalNativeConditionalKernels
