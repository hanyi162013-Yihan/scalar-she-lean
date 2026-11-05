module
public import SHE.SingleNativeIndependentExtension
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.SingleNativeGlobalFamily
open MeasureTheory PredictableL2 FiniteHaar DyadicApproximation OrthogonalItoChannels
open scoped NNReal ENNReal
local instance singleGlobal_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance singleGlobal_circleSecond:SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance singleGlobal_realSecond:SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance singleGlobal_realSigma:MeasurableSpace RealL2:=borel _
local instance singleGlobal_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance singleGlobal_bothSigma:MeasurableSpace (Both RealL2):=borel _
local instance singleGlobal_bothBorel:BorelSpace (Both RealL2):=⟨rfl⟩
variable {ι:Type} (Ω:ι→Type) [∀i,MeasurableSpace (Ω i)]
variable (F:∀i,Filtration ℝ≥0 (inferInstance:MeasurableSpace (Ω i)))
variable (μ:∀i,Measure (Ω i)) [∀i,IsProbabilityMeasure (μ i)] (H:ℝ≥0)
variable (J:∀i,StandardTerminalIto (C:=RealL2) (E:=ℝ) (F i) (μ i) H)

/-- Ordinary product construction on an independent COPY of each given
noise. No auxiliary SPDE solution or weak existence is requested. -/
def Products : Prop := ∀i,StandardIndependentProductIto (F i) (F i) (μ i) (μ i) H (J i) (J i)

def selected (P:Products Ω F μ H J) (i:ι) :
    IndependentProductItoData (F i) (F i) (μ i) (μ i) H (J i) (J i) :=
  Classical.choice ((P i).exists_data)

abbrev Space (i:ι) := IndependentNoiseCompletion.Space (μ i) (μ i)
def measure (i:ι) : Measure (Space Ω μ i) := IndependentNoiseCompletion.measure (μ i) (μ i)
instance probability (i:ι) : IsProbabilityMeasure (measure Ω μ i) := by
  unfold measure
  infer_instance
def filtration (i:ι) : Filtration ℝ≥0 (inferInstance:MeasurableSpace (Space Ω μ i)) :=
  IndependentNoiseCompletion.filtration (μ i) (μ i) (F i) (F i)

def physical (P:Products Ω F μ H J) (i:ι) :
    StandardTerminalIto (C:=Both RealL2) (E:=ℝ) (filtration Ω F μ i) (measure Ω μ i) H :=
  (selected Ω F μ H J P i).integral

variable (D:SmoothApproximation.ScalarData) (u₀:RealL2)
variable (S:∀i,SingleNativeHeatEquation.Data (F i) (μ i) H D (J i) u₀)

def model (P:Products Ω F μ H J) (i:ι) :
    OriginalNativeHeatEquation.Data (filtration Ω F μ i) (measure Ω μ i) H D
      (physical Ω F μ H J P i) u₀ :=
  SingleNativeIndependentExtension.of_integral (F i) (F i) (μ i) (μ i) H D (J i) u₀ (S i)
    (J i) (selected Ω F μ H J P i)

theorem same_law (P:Products Ω F μ H J) (i:ι) :
    NativePathLawComparison.law H (measure Ω μ i) (model Ω F μ H J D u₀ S P i).value
      (model Ω F μ H J D u₀ S P i).continuous=
    NativePathLawComparison.law H (μ i) (S i).value (S i).continuous :=
  IndependentNoiseCompletion.state_law (μ i) (μ i) H (S i).value (S i).continuous
    (((S i).predictable.mono (predictable_le_product (F i))).measurable)

theorem contains_null (i:ι) :
    NullCompleteFiltration.ContainsNullSets (filtration Ω F μ i) (measure Ω μ i) :=
  IndependentNoiseCompletion.contains_null (μ i) (μ i) (F i) (F i)
end SHE.SingleNativeGlobalFamily
