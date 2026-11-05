module

public import SHEStochastic.NativeSmoothRandomMildExistence
public import SHE.TimeDilationNaturality

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.NativeHeatNaturality
open MeasureTheory SHE SHE.PredictableL2 SHE.FiniteHaar SHE.DyadicApproximation
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩

variable {Ω ι κ : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι] [Countable κ]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ RealHaarInput)
  (b : HilbertBasis κ ℝ RealL2)

/-- Naturality of the actual Picard-construction integral follows from
the existing Hilbert lift, with identity restriction removed exactly. -/
theorem scalarNaturality : NativeObservationNaturality.StandardScalarNaturality
    (NativeSmoothRandomMildExistence.integral F μ H P e (LinearIsometry.id : RealHaarInput →ₗᵢ[ℝ] RealHaarInput) b)
    (FiniteCylindricalIto.terminalIto P.toCoordinates e) := by
  constructor
  intro L v
  exact (HilbertTerminalIto.commutes F μ H b
    (restrictNoise (FiniteCylindricalIto.terminalIto P.toCoordinates e)
      (LinearIsometry.id : RealHaarInput →ₗᵢ[ℝ] RealHaarInput)) L v).trans
      (restrictNoise_id (FiniteCylindricalIto.terminalIto P.toCoordinates e) _)

theorem clocked (c : ℝ≥0) (hc : 0 < c) : NativeObservationNaturality.StandardScalarNaturality
    (PredictableTimeDilation.integral F μ c hc H
      (NativeSmoothRandomMildExistence.integral F μ H P e (LinearIsometry.id : RealHaarInput →ₗᵢ[ℝ] RealHaarInput) b))
    (PredictableTimeDilation.integral F μ c hc H (FiniteCylindricalIto.terminalIto P.toCoordinates e)) :=
  PredictableTimeDilation.scalarNaturality F μ c hc H _ _ (scalarNaturality F μ H P e b)

end SHEStochastic.NativeHeatNaturality
