module
public import SHE.SingleNativeIndependentExtension
public import SHE.GivenOriginalNativeLocalUniqueness
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.SingleNativeProductFamily
open MeasureTheory PredictableL2 NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance family_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance family_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance family_circleSecond:SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=1)).repr.toHomeomorph.secondCountableTopology
local instance family_realSecond:SecondCountableTopology RealL2:=realCircleIdentification.toHomeomorph.secondCountableTopology
local instance family_realSigma:MeasurableSpace RealL2:=borel _
local instance family_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance family_bothSigma:MeasurableSpace (Both RealL2):=borel _
local instance family_bothBorel:BorelSpace (Both RealL2):=⟨rfl⟩
local instance family_haarSigma:MeasurableSpace RealHaarInput:=borel _
local instance family_haarBorel:BorelSpace RealHaarInput:=⟨rfl⟩
variable {ι:Type}(Ω:ι→Type)[∀i,MeasurableSpace (Ω i)]
variable (𝓕:∀i,Filtration ℝ≥0 (inferInstance:MeasurableSpace (Ω i)))
  (μ:∀i,Measure (Ω i))[∀i,IsProbabilityMeasure (μ i)](h:ℝ≥0)
variable (J:∀i,StandardTerminalIto (C:=RealL2) (E:=ℝ)
  (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos))
  (μ i) (NativeClock.rate*h))

/-- Exactly the ordinary package1 constructor at each given noise and
an independent copy of that SAME noise. -/
def Products:Prop:=∀i,StandardIndependentProductIto
  (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos))
  (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos))
  (μ i) (μ i) (NativeClock.rate*h) (J i) (J i)

def selected(P:Products Ω 𝓕 μ h J)(i:ι):IndependentProductItoData
    (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos))
    (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos))
    (μ i) (μ i) (NativeClock.rate*h) (J i) (J i):=
  Classical.choice ((P i).exists_data)

def measure(i:ι):Measure (IndependentNoiseCompletion.Space (μ i) (μ i)):=IndependentNoiseCompletion.measure (μ i) (μ i)
instance probability(i:ι):IsProbabilityMeasure (measure Ω μ i):=
  inferInstanceAs (IsProbabilityMeasure (IndependentNoiseCompletion.measure (μ i) (μ i)))

def filtration(i:ι):Filtration ℝ≥0 (inferInstance:MeasurableSpace (IndependentNoiseCompletion.Space (μ i) (μ i))):=
  IndependentNoiseCompletion.filtration (μ i) (μ i) (𝓕 i) (𝓕 i)

theorem filtration_clock(i:ι):
    PredictableTimeDilation.filtration (filtration Ω 𝓕 μ i)
      (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)=
    IndependentNoiseCompletion.filtration (μ i) (μ i)
      (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos))
      (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)):=rfl

def physical(P:Products Ω 𝓕 μ h J)(i:ι):StandardTerminalIto (C:=Both RealL2) (E:=ℝ)
    (PredictableTimeDilation.filtration (filtration Ω 𝓕 μ i)
      (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (measure Ω μ i) (NativeClock.rate*h):=
  (selected Ω 𝓕 μ h J P i).integral

variable (D:SmoothApproximation.ScalarData)(u₀:RealL2)
variable (U:∀i,SingleNativeHeatEquation.Data
  (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos))
  (μ i) (NativeClock.rate*h) D (J i) u₀)

def augmented(P:Products Ω 𝓕 μ h J)(i:ι):OriginalNativeHeatEquation.Data
    (PredictableTimeDilation.filtration (filtration Ω 𝓕 μ i)
      (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (measure Ω μ i) (NativeClock.rate*h)
    D (physical Ω 𝓕 μ h J P i) u₀:=
  SingleNativeIndependentExtension.of_integral
    (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos))
    (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos))
    (μ i) (μ i) (NativeClock.rate*h) D (J i) u₀ (U i) (J i) (selected Ω 𝓕 μ h J P i)

def driver(P:Products Ω 𝓕 μ h J)(i:ι):StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ)
    (PredictableTimeDilation.filtration (filtration Ω 𝓕 μ i)
      (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (measure Ω μ i) (NativeClock.rate*h):=
  PredictableScalarHaarRotation.integral
    (PredictableTimeDilation.filtration (filtration Ω 𝓕 μ i)
      (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (measure Ω μ i) (NativeClock.rate*h) D
      (Function.uncurry (augmented Ω 𝓕 μ h J D u₀ U P i).value)
      (augmented Ω 𝓕 μ h J D u₀ U P i).predictable (physical Ω 𝓕 μ h J P i)

theorem same_law(P:Products Ω 𝓕 μ h J)(i:ι):
    NativePathLawComparison.law (NativeClock.rate*h) (measure Ω μ i)
      (augmented Ω 𝓕 μ h J D u₀ U P i).value (augmented Ω 𝓕 μ h J D u₀ U P i).continuous=
    NativePathLawComparison.law (NativeClock.rate*h) (μ i) (U i).value (U i).continuous:=
  IndependentNoiseCompletion.state_law (μ i) (μ i) (NativeClock.rate*h) (U i).value (U i).continuous
    (((U i).predictable.mono (predictable_le_product
      (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)))).measurable)

theorem contains_null(i:ι):NullCompleteFiltration.ContainsNullSets
    (PredictableTimeDilation.filtration (filtration Ω 𝓕 μ i)
      (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (measure Ω μ i):=
  IndependentNoiseCompletion.contains_null (μ i) (μ i)
    (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos))
    (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos))
end SHE.SingleNativeProductFamily
