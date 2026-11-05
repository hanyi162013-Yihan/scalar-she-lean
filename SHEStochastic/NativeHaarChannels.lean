module

public import SHEStochastic.NativeScalarModel
public import SHEStochastic.NativeChangedHilbertBDG
public import SHEStochastic.NativeHilbertBDG
public import SHE.NativeObservationNaturality

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.NativeHaarChannels
open MeasureTheory SHE SHE.PredictableL2 SHE.FiniteHaar SHE.HilbertColumns SHE.OrthogonalItoChannels
open SHE.DyadicApproximation SHE.NativeObservationNaturality
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology LowBands.StateL2 :=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput) := borel _
local instance : BorelSpace (Both RealHaarInput) := ⟨rfl⟩

variable {Ω : Type} [MeasurableSpace Ω]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) F μ H)

/-- The two Hilbert lifts and exactly the estimates used by the scalar
comparison. Both channels are tied to the given same scalar integral. -/
structure Channels where
  I₀ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) F μ H
  I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) F μ H
  natural₀ : StandardScalarNaturality I₀ (leftIntegral F μ H J)
  natural₁ : StandardScalarNaturality I₁ (rightIntegral F μ H J)
  bdg₀ : StandardTerminalBDG16 I₀ (NativeScalarBDG.constant 3)
  bdg₁ : StandardTerminalBDG16 I₁ (NativeScalarBDG.constant 3)
  bdgNext : StandardTerminalBDGPower 1 I₁ 1

/-- Build the required channels from existing scalar-to-Hilbert lifts. -/
def channels (M : NativeScalarModel.Model J) : Channels J := by
  let hb := exists_hilbertBasis (𝕜 := ℝ) (E := RealL2)
  let κ := Classical.choose hb
  let b : HilbertBasis κ ℝ RealL2 := Classical.choose (Classical.choose_spec hb)
  letI : Countable κ := hilbertBasis_countable b
  let I0 := HilbertTerminalIto.terminalIto F μ H b (restrictNoise J (left (C := RealHaarInput)))
  let I1 := HilbertTerminalIto.terminalIto F μ H b (restrictNoise J (right (C := RealHaarInput)))
  refine ⟨I0, I1, ?_, ?_, ?_, ?_, BDGSecondMoment.power_one I1⟩
  · constructor
    intro L u
    exact (HilbertTerminalIto.commutes F μ H b _ L u).trans
      (NoiseRestrictionBounds.integral_eq_rotation J left (left_measurable F) _)
  · constructor
    intro L u
    exact (HilbertTerminalIto.commutes F μ H b _ L u).trans
      (NoiseRestrictionBounds.integral_eq_rotation J right (right_measurable F) _)
  · dsimp only [I0]
    rw [M.identifies]
    exact NativeHilbertBDG.hilbertBDG16 M.family M.basis (left (C := RealHaarInput)) b
  · dsimp only [I1]
    rw [M.identifies]
    exact NativeHilbertBDG.hilbertBDG16 M.family M.basis (right (C := RealHaarInput)) b

theorem changed (M : NativeScalarModel.Model J) : StandardChangedHilbertBDG F μ H J := by
  rw [M.identifies]
  exact NativeChangedHilbertBDG.standard M.family M.basis

end SHEStochastic.NativeHaarChannels
