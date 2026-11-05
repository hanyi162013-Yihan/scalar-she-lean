module

public import SHE.ScaledLpNaturality
public import SHE.TimeDilationIto
public import SHE.NativeObservationNaturality

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.PredictableTimeDilation
open MeasureTheory PredictableL2 NativeObservationNaturality
open scoped NNReal ENNReal
variable {Ω E D : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup D] [InnerProductSpace ℝ D]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ]
variable (c : ℝ≥0) (hc : 0<c) (h : ℝ≥0)

theorem processIsometry_compLpL (L : E→L[ℝ]D)
    (v : Process (E := E) (filtration 𝓕 (clock c hc)) μ (c*h)) :
    (L.compLpL 2 ((energyMeasure μ h).trim (predictable_le_product 𝓕)))
      (processIsometry 𝓕 μ c hc h v)=
    processIsometry 𝓕 μ c hc h
      ((L.compLpL 2 ((energyMeasure μ (c*h)).trim
        (predictable_le_product (filtration 𝓕 (clock c hc))))) v) :=
  @ScaledLpPull.isometry_compLpL (ℝ≥0×Ω) (ℝ≥0×Ω) E D 𝓕.predictable
    (filtration 𝓕 (clock c hc)).predictable _ _ _ _
    ((energyMeasure μ h).trim (predictable_le_product 𝓕))
    ((energyMeasure μ (c*h)).trim (predictable_le_product (filtration 𝓕 (clock c hc))))
    (c:ℝ) hc (fun p => (clock c hc p.1,p.2)) (predictableMeasure_clock_preserving 𝓕 μ c hc h)
    (@MeasurableEquiv.measurableEmbedding _ _ 𝓕.predictable (filtration 𝓕 (clock c hc)).predictable
      (predictableEquiv 𝓕 (clock c hc))) L v

local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
local instance : MeasurableSpace FiniteHaar.RealHaarInput := borel _
local instance : BorelSpace FiniteHaar.RealHaarInput := ⟨rfl⟩

/-- Ordinary scalar/Hilbert Itô naturality is inherited by the same
clocked integral. It is not postulated a second time in native units. -/
theorem scalarNaturality [IsProbabilityMeasure μ]
    (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := LowBands.StateL2) 𝓕 μ h)
    (J : StandardTerminalIto (C := FiniteHaar.RealHaarInput) (E := ℝ) 𝓕 μ h)
    (hIJ : StandardScalarNaturality I J) :
    StandardScalarNaturality (integral 𝓕 μ c hc h I) (integral 𝓕 μ c hc h J) := by
  constructor
  intro L v
  change (L.compLpL 2 μ) (I.integral (processIsometry 𝓕 μ c hc h v))=
    J.integral (processIsometry 𝓕 μ c hc h
      (((HilbertColumns.mapCLM L).compLpL 2 ((energyMeasure μ (c*h)).trim
        (predictable_le_product (filtration 𝓕 (clock c hc))))) v))
  rw [hIJ.commutes]
  exact congrArg J.integral (processIsometry_compLpL 𝓕 μ c hc h (HilbertColumns.mapCLM L) v)

end SHE.PredictableTimeDilation
