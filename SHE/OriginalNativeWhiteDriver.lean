module
public import SHE.OriginalSingleHaarInputs
public import SHE.RotatedLevy
public import SHE.ItoLocalityTransport
public import SHE.DeterministicItoShiftRotation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.OriginalNativeWhiteDriver
open MeasureTheory PredictableL2 FiniteHaar DyadicApproximation OrthogonalItoChannels
open scoped NNReal ENNReal
local instance nativeWhite_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeWhite_circleSecond:SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance nativeWhite_realSecond:SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance nativeWhite_realSigma:MeasurableSpace RealL2:=borel _
local instance nativeWhite_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance nativeWhite_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance nativeWhite_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance nativeWhite_bothSigma:MeasurableSpace (Both RealL2):=borel _
local instance nativeWhite_bothBorel:BorelSpace (Both RealL2):=⟨rfl⟩
variable {Ω:Type*} [MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω) [IsProbabilityMeasure μ] (H:ℝ≥0)
variable (B:StandardTerminalIto (C:=Both RealL2) (E:=ℝ) 𝓕 μ H)

def integral : StandardTerminalIto (C:=RealHaarInput) (E:=ℝ) 𝓕 μ H :=
  OriginalSingleHaarInputs.integral 𝓕 μ H (leftIntegral 𝓕 μ H B)

theorem bdg (C:ℝ≥0) (hB:StandardTerminalBDG16 B C) :
    StandardTerminalBDG16 (integral 𝓕 μ H B) C :=
  PredictableItoRotation.bdg16 𝓕 μ H
    (fun _=>OriginalNativeFrozenRows.coordinates.toLinearIsometry)
    (OriginalNativeFrozenRows.coordinates.continuous.measurable.comp measurable_snd)
    (leftIntegral 𝓕 μ H B) C
    (PredictableItoRotation.bdg16 𝓕 μ H (fun _=>left (C:=RealL2)) (left_measurable 𝓕) B C hB)

theorem levy (hB:StandardTerminalLevy B) : StandardTerminalLevy (integral 𝓕 μ H B) :=
  PredictableItoRotation.levy 𝓕 μ H
    (fun _=>OriginalNativeFrozenRows.coordinates.toLinearIsometry)
    (OriginalNativeFrozenRows.coordinates.continuous.measurable.comp measurable_snd)
    (leftIntegral 𝓕 μ H B)
    (PredictableItoRotation.levy 𝓕 μ H (fun _=>left (C:=RealL2)) (left_measurable 𝓕) B hB)

theorem left_locality (hB:StandardTerminalPastLocality B) :
    StandardTerminalPastLocality (leftIntegral 𝓕 μ H B) :=
  ItoLocalityTransport.rotation 𝓕 μ H (fun _=>left (C:=RealL2)) (left_measurable 𝓕) B hB

/-- The white driver of the actual restarted original equation is
exactly the restart of its original white driver. Both constant rotations
commute with the SAME physical time-window extension. -/
theorem shifted (v h:ℝ≥0) (hvh:v+h≤H) :
    integral (DeterministicItoShift.filtration 𝓕 v) μ h
      (DeterministicItoShift.integral 𝓕 μ H v h hvh B)=
    DeterministicItoShift.integral 𝓕 μ H v h hvh (integral 𝓕 μ H B) := by
  have hl := DeterministicItoShiftRotation.integral 𝓕 μ H v h hvh (left (C:=RealL2)) B
  have hw := DeterministicItoShiftRotation.integral 𝓕 μ H v h hvh
    OriginalNativeFrozenRows.coordinates.toLinearIsometry (leftIntegral 𝓕 μ H B)
  change leftIntegral (DeterministicItoShift.filtration 𝓕 v) μ h
      (DeterministicItoShift.integral 𝓕 μ H v h hvh B)=
    DeterministicItoShift.integral 𝓕 μ H v h hvh (leftIntegral 𝓕 μ H B) at hl
  change OriginalSingleHaarInputs.integral (DeterministicItoShift.filtration 𝓕 v) μ h
      (DeterministicItoShift.integral 𝓕 μ H v h hvh (leftIntegral 𝓕 μ H B))=
    DeterministicItoShift.integral 𝓕 μ H v h hvh (integral 𝓕 μ H B) at hw
  change OriginalSingleHaarInputs.integral (DeterministicItoShift.filtration 𝓕 v) μ h
      (leftIntegral (DeterministicItoShift.filtration 𝓕 v) μ h
        (DeterministicItoShift.integral 𝓕 μ H v h hvh B))=_
  rw [hl]
  exact hw
end SHE.OriginalNativeWhiteDriver
