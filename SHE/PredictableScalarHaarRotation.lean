module
public import SHE.ScalarHaarRotationMeasurable
public import SHE.ScalarHaarHeatRows
public import SHE.TwoChannelItoRows
public import SHE.NativeObservationProcess
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
namespace SHE.PredictableScalarHaarRotation
open MeasureTheory CircleHeat FiniteHaar DyadicApproximation AddCircle PredictableL2
open NoiseSplitting OrthogonalItoChannels AdditivePhysicalFactor StoppedFourier
open scoped NNReal ENNReal
local instance : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 :=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance (ell M : ℝ) : MeasurableSpace (EllipticField ell M) := Subtype.instMeasurableSpace
local instance (ell M : ℝ) : BorelSpace (EllipticField ell M) := by infer_instance
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (D : SmoothApproximation.ScalarData)
variable (U : ℝ≥0 × Ω → RealL2) (hU : StronglyMeasurable[𝓕.predictable] U)

def field (p : ℝ≥0 × Ω) : Both RealHaarInput →ₗᵢ[ℝ] Both RealL2 :=
  (ScalarHaarRotation.rotation D (U p)).toLinearIsometry

include hU in
theorem field_measurable : @Measurable ((ℝ≥0 × Ω) × Both RealHaarInput) (Both RealL2)
    (𝓕.predictable.prod inferInstance) inferInstance (fun p => field D U p.1 p.2) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  have hm := (ScalarHaarRotation.action_measurable D).comp
    ((hU.measurable.comp measurable_fst).prodMk measurable_snd)
  exact hm

def integral (B : StandardTerminalIto (C:=Both RealL2) (E:=ℝ) 𝓕 μ H) :
    StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H :=
  PredictableItoRotation.integral 𝓕 μ H (field D U) (field_measurable 𝓕 D U hU) B

def residual (p : ℝ≥0 × Ω) : EllipticField D.ell D.cap := ScalarHaarRotation.residual D (U p)

include hU in
theorem residual_predictable : StronglyMeasurable[𝓕.predictable] (residual D U) :=
  ((ScalarHaarRotation.residual_measurable D).comp hU.measurable).stronglyMeasurable

def additiveRow {T t : ℝ} (ht : t < T) (x : HeatCircle) : Process (E:=RealHaarInput) 𝓕 μ H :=
  NativeObservationProcess.process 𝓕 μ H
    (sq_pos_of_pos (ScalarHaarRotation.amplitude_pos D)) (sq_nonneg _)
    (fun _ => AdditiveHaarForcing.constantField ((ScalarHaarRotation.amplitude D)^2)
      (sq_pos_of_pos (ScalarHaarRotation.amplitude_pos D))) stronglyMeasurable_const ht x

def residualRow {T t : ℝ} (ht : t < T) (x : HeatCircle) : Process (E:=RealHaarInput) 𝓕 μ H :=
  NativeObservationProcess.process 𝓕 μ H D.ell_pos D.cap_nonneg (residual D U)
    (residual_predictable 𝓕 D U hU) ht x

/-- An actual original physical row, represented by a genuine L2 input.
The following theorem identifies its literal g(U) spatial coefficient. -/
def originalRow {T t : ℝ} (ht : t < T) (x : HeatCircle) : Process (E:=Both RealL2) 𝓕 μ H :=
  PredictableItoRotation.processIsometry 𝓕 μ H (field D U) (field_measurable 𝓕 D U hU)
    (TwoChannelItoRows.block 𝓕 μ H (additiveRow 𝓕 μ H D ht x) (residualRow 𝓕 μ H D U hU ht x))

/-- Exact same-integral recovery of the original physical observation;
the two split channels are not independently chosen noises. -/
theorem integral_originalRow (B : StandardTerminalIto (C:=Both RealL2) (E:=ℝ) 𝓕 μ H)
    {T t : ℝ} (ht : t < T) (x : HeatCircle) :
    B.integral (originalRow 𝓕 μ H D U hU ht x) =
      (leftIntegral 𝓕 μ H (integral 𝓕 μ H D U hU B)).integral (additiveRow 𝓕 μ H D ht x) +
      (rightIntegral 𝓕 μ H (integral 𝓕 μ H D U hU B)).integral (residualRow 𝓕 μ H D U hU ht x) := by
  rw [← TwoChannelItoRows.integral_block]
  rfl
end SHE.PredictableScalarHaarRotation
