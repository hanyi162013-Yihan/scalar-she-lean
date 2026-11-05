module

public import SHEStochastic.NativeHilbertBDG
public import SHEStochastic.HilbertIntegralUniqueness
public import SHEStochastic.CountableHilbertBasis
public import SHE.StandardRecognizedHilbertBDG

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.NativeRecognizedHilbertBDG
open MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns SHE.OrthogonalItoChannels
open SHE.FiniteHaar
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput) := borel _
local instance : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance : SecondCountableTopology LowBands.StateL2 :=
  realCircleIdentification.toHomeomorph.secondCountableTopology

/-- EXACT original recognized-Hilbert BDG interface for the constructed
two-channel integral. Both Hilbert integrals may be any integrals with
the specified scalar naturality. Their estimates follow from the proved
native Hilbert bound and uniqueness under scalar observations. -/
theorem standardRecognizedHilbertBDG {Ω β : Type*} [MeasurableSpace Ω]
    [Countable β] [DecidableEq β]
    {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : ℝ≥0} (P : FiniteScalarIto.Family F μ H β)
    (e : HilbertBasis β ℝ (Both RealHaarInput)) :
    StandardRecognizedHilbertBDG F μ H (FiniteCylindricalIto.terminalIto P.toCoordinates e) := by
  intro _ _ A0 A1 hA0 hA1
  let K := FiniteCylindricalIto.terminalIto P.toCoordinates e
  obtain ⟨κ, b, _⟩ := exists_hilbertBasis (𝕜 := ℝ) (E := LowBands.StateL2)
  letI : Countable κ := hilbertBasis_countable b
  let I0 := HilbertTerminalIto.terminalIto F μ H b (restrictNoise K (left (C := RealHaarInput)))
  let I1 := HilbertTerminalIto.terminalIto F μ H b (restrictNoise K (right (C := RealHaarInput)))
  have h0 := NativeHilbertBDG.hilbertBDG16 P e (left (C := RealHaarInput)) b
  have h1 := NativeHilbertBDG.hilbertBDG16 P e (right (C := RealHaarInput)) b
  have hc0 (L : LowBands.StateL2 →L[ℝ] ℝ) (u : Process (E := RealHaarIntegrand.Columns) F μ H) :
      (L.compLpL 2 μ) (I0.integral u) = (leftIntegral F μ H K).integral
        (((mapCLM L).compLpL 2 ((energyMeasure μ H).trim (predictable_le_product F))) u) :=
    (HilbertTerminalIto.commutes F μ H b _ L u).trans
      (NoiseRestrictionBounds.integral_eq_rotation K left (left_measurable F) _)
  have hc1 (L : LowBands.StateL2 →L[ℝ] ℝ) (u : Process (E := RealHaarIntegrand.Columns) F μ H) :
      (L.compLpL 2 μ) (I1.integral u) = (rightIntegral F μ H K).integral
        (((mapCLM L).compLpL 2 ((energyMeasure μ H).trim (predictable_le_product F))) u) :=
    (HilbertTerminalIto.commutes F μ H b _ L u).trans
      (NoiseRestrictionBounds.integral_eq_rotation K right (right_measurable F) _)
  refine ⟨NativeScalarBDG.constant 3, NativeScalarBDG.constant 3, ?_, ?_⟩
  · intro u
    rw [HilbertIntegralUniqueness.integral_eq b (A0.integral u) (I0.integral u)
      (fun j ↦ (hA0.commutes (innerSL ℝ (b j)) u).trans (hc0 _ u).symm)]
    exact h0 u
  · intro u
    rw [HilbertIntegralUniqueness.integral_eq b (A1.integral u) (I1.integral u)
      (fun j ↦ (hA1.commutes (innerSL ℝ (b j)) u).trans (hc1 _ u).symm)]
    exact h1 u

end SHEStochastic.NativeRecognizedHilbertBDG
