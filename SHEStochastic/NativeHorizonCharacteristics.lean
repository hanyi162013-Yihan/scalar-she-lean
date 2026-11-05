module

public import SHEStochastic.NativeCrossCompensator
public import SHEStochastic.NativeBrownianCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.NativeHorizonCharacteristics
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

theorem energy_clip (r : Process (E := C) F μ H) (t : ℝ≥0) :
    PredictableBracket.energy r (min t H) =ᵐ[μ] PredictableBracket.energy r t := by
  have hh := PredictableBracket.stopped_eq r (min t H)
  rw [NNReal.coe_min, RawCylindricalCoordinates.stop_min] at hh
  exact hh.symm.trans (PredictableBracket.stopped_eq r t)

theorem cross_clip (r v : Process (E := C) F μ H) (t : ℝ≥0) :
    NativeCrossCompensator.value r v (min t H) =ᵐ[μ] NativeCrossCompensator.value r v t := by
  filter_upwards [energy_clip r t, energy_clip v t, energy_clip (r-v) t] with sample hr hv hd
  change (_+_-_)/2 = (_+_-_)/2
  rw [hr, hv, hd]

/-- When the given Brownian coordinates are held at the native
horizon, the usual coordinate integral identity holds at all clocks. -/
theorem coordinates (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (hclip : ∀ i t, P.W i t = P.W i (min t H)) (i : ι) (t : ℝ≥0) :
    P.W i t =ᵐ[μ] (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
      (StoppedItoInputs.stop F μ H t (RotatedCylindricalCoordinates.constant F μ H (e i))) := by
  have hh := FiniteCylindricalIto.coordinate_integral P e i (min t H) (min_le_right _ _)
  rw [NNReal.coe_min, RawCylindricalCoordinates.stop_min] at hh
  rw [hclip i t]
  exact hh.symm

end SHEStochastic.NativeHorizonCharacteristics
