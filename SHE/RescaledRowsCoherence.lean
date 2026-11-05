module

public import SHE.InterpolatedPredictableRows
public import SHE.StoppedDampingClock
public import SHE.StoppedInputAlgebra
public import SHE.RotatedItoAlgebra

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.RescaledRowsCoherence
open MeasureTheory PredictableL2 StoppedItoInputs PredictableItoRotation OrthogonalItoChannels
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
local instance rescaledRowsCoherence_blockSigma : MeasurableSpace (Both C) := borel _
local instance rescaledRowsCoherence_blockBorel : BorelSpace (Both C) := ⟨rfl⟩
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

/-- Changing the auxiliary normalization horizon of the integrating
factor preserves every earlier stopped ORIGINAL input. -/
theorem stop_rescaled {Λ : ℝ} (hΛ : 0≤Λ) (b c : ℝ≥0) (hcb : c≤b)
    (u v : Process (E:=C) 𝓕 μ H) :
    stop 𝓕 μ H (c:ℝ) (InterpolatedPredictableRows.rescaledDifference 𝓕 μ H hΛ b u v)=
      InterpolatedPredictableRows.rescaledDifference 𝓕 μ H hΛ c
        (stop 𝓕 μ H c u) (stop 𝓕 μ H c v) := by
  unfold InterpolatedPredictableRows.rescaledDifference
  rw [←RotatedItoAlgebra.map_stop,StoppedInputAlgebra.stop_smul,
    ←StoppedDampingClock.integrating_factor 𝓕 μ H hΛ b c hcb]
  rw [←StoppedDampingClock.stop_sub]
  rfl

end SHE.RescaledRowsCoherence
