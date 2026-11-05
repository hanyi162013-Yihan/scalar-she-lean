module

public import SHEStochastic.NativeFourierMixedTests
public import SHEStochastic.NativeHorizonCharacteristics

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.CanonicalNativeFourierInput
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open CanonicalStateDriverFiltration
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {V ι : Type*} [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B) (H : ℝ≥0)
  (Q : Measure (CanonicalFourierFluctuation.Space (ι := ι) H)) [IsProbabilityMeasure Q]
  (a : ℂ →L[ℝ] ℝ) (n : ℤ)

local instance : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩

def input : Process (E := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) (filtration H) Q H :=
  BoundedFourierInput.input (filtration H) Q H (state H) (state_predictable H) hG hβ hβ1 B hb a n

/-- The path-law square compensator and the actual canonical native
input energy agree at every clock, including after the capped horizon. -/
theorem energy (t : ℝ≥0) :
    (fun x ↦ NativeFourierSquareTests.compensator (ι := ι) hG hβ hβ1 B hb a n H t x) =ᵐ[Q]
      PredictableBracket.energy (input hG hβ hβ1 B hb H Q a n) t := by
  filter_upwards [NativeFourierCompensatorValue.energy_ae hG hβ hβ1 B hb a n (filtration H)
    Q H (state H) (state_predictable H), NativeHorizonCharacteristics.energy_clip
      (input hG hβ hβ1 B hb H Q a n) t] with x hx hc
  change CanonicalFourierCompensator.value H (2*(n : ℝ)^2) _ _ t x = _
  rw [CanonicalFourierCompensator.canonical_value, ← hx (min t H) (min_le_right _ _)]
  exact hc

theorem mixed [SecondCountableTopology (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))]
    (b : Lp V 2 (haarAddCircle (T := 2 * Real.pi))) (t : ℝ≥0) :
    (fun x ↦ NativeFourierMixedTests.compensator (ι := ι) hG hβ hβ1 B hb a n b H t x) =ᵐ[Q]
      NativeCrossCompensator.value (input hG hβ hβ1 B hb H Q a n)
        (RotatedCylindricalCoordinates.constant (filtration H) Q H b) t := by
  filter_upwards [NativeFourierCompensatorValue.mixed_ae hG hβ hβ1 B hb a n (filtration H)
    Q H (state H) (state_predictable H) b, NativeHorizonCharacteristics.cross_clip
      (input hG hβ hβ1 B hb H Q a n) (RotatedCylindricalCoordinates.constant (filtration H) Q H b) t]
      with x hx hc
  change CanonicalFourierCompensator.value H ((n : ℝ)^2) _ _ t x = _
  rw [CanonicalFourierCompensator.canonical_value, ← hx (min t H) (min_le_right _ _)]
  exact hc

end SHEStochastic.CanonicalNativeFourierInput
