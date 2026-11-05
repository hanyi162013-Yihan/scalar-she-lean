module

public import SHEStochastic.MatrixFourierSquareTests
public import SHEStochastic.MatrixFourierMixedTests
public import SHEStochastic.NativeHorizonCharacteristics

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.MatrixCanonicalFourierInput
open MeasureTheory SHE SHE.PredictableL2 MatrixInfiniteHaar MatrixFourierCoordinates CanonicalStateDriverFiltration
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d : Type*} [Fintype d] [DecidableEq d]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩
variable (G : MatrixNonlinearCoefficient.Coefficient d) {C β : ℝ≥0}
    (hG : HolderWith C β G.value) (hβ : 0 < β) (hβ1 : β ≤ 1) (H : ℝ≥0)
    (Q : Measure (CanonicalContinuousStateDriver.Space (E := Physical (d := d)) (ι := d×FiniteHaar.HaarNode) H))
    [IsProbabilityMeasure Q] (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ)

def input : Process (E := Input (d := d)) (filtration H) Q H :=
  MatrixFourierInput.input (filtration H) Q H G hG hβ hβ1
    (fun p => state H p.1 p.2) (state_predictable H) i a n

/-- The path-law square compensator is the actual canonical native
input energy, including after the capped horizon. -/
theorem energy (t : ℝ≥0) :
    (fun x => MatrixFourierSquareTests.compensator H G hG hβ hβ1 i a n t x) =ᵐ[Q]
      PredictableBracket.energy (input G hG hβ hβ1 H Q i a n) t := by
  filter_upwards [MatrixFourierCompensator.energy_ae (filtration H) Q H G hG hβ hβ1
    (fun p => state H p.1 p.2) (state_predictable H) i a n,
    NativeHorizonCharacteristics.energy_clip (input G hG hβ hβ1 H Q i a n) t] with x hx hc
  change CanonicalFourierCompensator.value H (2*(n : ℝ)^2) _ _ t x=_
  rw [CanonicalFourierCompensator.canonical_value,← hx (min t H) (min_le_right _ _)]
  exact hc

/-- The same equality for every retained canonical Brownian coordinate. -/
theorem mixed (k : d×FiniteHaar.HaarNode) (t : ℝ≥0) :
    (fun x => MatrixFourierMixedTests.compensator H G hG hβ hβ1 i a n k t x) =ᵐ[Q]
      NativeCrossCompensator.value (input G hG hβ hβ1 H Q i a n)
        (RotatedCylindricalCoordinates.constant (filtration H) Q H (MatrixPredictableHaarRotation.basis k)) t := by
  filter_upwards [MatrixFourierCompensator.mixed_ae (filtration H) Q H G hG hβ hβ1
    (fun p => state H p.1 p.2) (state_predictable H) i a n (MatrixPredictableHaarRotation.basis k),
    NativeHorizonCharacteristics.cross_clip (input G hG hβ hβ1 H Q i a n)
      (RotatedCylindricalCoordinates.constant (filtration H) Q H (MatrixPredictableHaarRotation.basis k)) t] with x hx hc
  change CanonicalFourierCompensator.value H ((n : ℝ)^2) _ _ t x=_
  rw [CanonicalFourierCompensator.canonical_value,← hx (min t H) (min_le_right _ _)]
  exact hc

end SHEStochastic.MatrixCanonicalFourierInput
