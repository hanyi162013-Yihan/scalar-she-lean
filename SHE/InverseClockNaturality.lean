module

public import SHE.TimeDilationNaturality
public import SHE.TimeDilationRoundTrip
public import SHE.OrthogonalItoChannels

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
variable (c : ℝ≥0) (hc : 0 < c) (h : ℝ≥0)

/-- Bounded linear maps commute with the literal inverse Brownian clock. -/
theorem processEquivalence_symm_compLpL (L : E →L[ℝ] D)
    (v : Process (E := E) 𝓕 μ h) :
    (L.compLpL 2 ((energyMeasure μ (c*h)).trim
      (predictable_le_product (filtration 𝓕 (clock c hc)))))
        ((processEquivalence 𝓕 μ c hc h).symm v) =
    (processEquivalence 𝓕 μ c hc h).symm
      ((L.compLpL 2 ((energyMeasure μ h).trim (predictable_le_product 𝓕))) v) := by
  apply (processEquivalence (C := D) 𝓕 μ c hc h).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  change processIsometry 𝓕 μ c hc h
    ((L.compLpL 2 ((energyMeasure μ (c*h)).trim
      (predictable_le_product (filtration 𝓕 (clock c hc)))))
        ((processEquivalence 𝓕 μ c hc h).symm v)) = _
  rw [← processIsometry_compLpL]
  rw [← processEquivalence_apply, LinearIsometryEquiv.apply_symm_apply]

local instance inverseClockNaturality_local0 : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance inverseClockNaturality_local1 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance inverseClockNaturality_local2 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
local instance inverseClockNaturality_local3 : MeasurableSpace FiniteHaar.RealHaarInput := borel _
local instance inverseClockNaturality_local4 : BorelSpace FiniteHaar.RealHaarInput := ⟨rfl⟩

/-- Ordinary scalar/Hilbert naturality passes to the SAME inverse-clock
integrals; no second naturality hypothesis is introduced. -/
theorem inverse_scalarNaturality [IsProbabilityMeasure μ]
    (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := LowBands.StateL2)
      (filtration 𝓕 (clock c hc)) μ (c*h))
    (J : StandardTerminalIto (C := FiniteHaar.RealHaarInput) (E := ℝ)
      (filtration 𝓕 (clock c hc)) μ (c*h))
    (hIJ : StandardScalarNaturality I J) :
    StandardScalarNaturality (inverseIntegral 𝓕 μ c hc h I)
      (inverseIntegral 𝓕 μ c hc h J) := by
  constructor
  intro L v
  change (L.compLpL 2 μ) (I.integral ((processEquivalence 𝓕 μ c hc h).symm v)) =
    J.integral ((processEquivalence 𝓕 μ c hc h).symm
      (((HilbertColumns.mapCLM L).compLpL 2
        ((energyMeasure μ h).trim (predictable_le_product 𝓕))) v))
  rw [hIJ.commutes]
  exact congrArg J.integral
    (processEquivalence_symm_compLpL 𝓕 μ c hc h (HilbertColumns.mapCLM L) v)

end SHE.PredictableTimeDilation
