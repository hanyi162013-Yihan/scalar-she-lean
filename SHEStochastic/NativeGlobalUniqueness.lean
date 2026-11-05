module

public import SHEStochastic.NativeSingleGlobalInputs

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.NativeGlobalUniqueness
open MeasureTheory SHE SHE.DyadicApproximation SHE.FiniteHaar
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

/-- Native bounded scalar uniqueness on every positive finite horizon.
Independent products and conditional local stochastic packages are all
constructed for the same supplied solutions and integral maps. -/
theorem laws_eq {ι : Type} [Fintype ι] [Nonempty ι]
    (Ω : ι → Type) [∀ i, MeasurableSpace (Ω i)]
    (F : ∀ i, Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω i)))
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (H : ℝ≥0) (hH : 0<H) (D : SmoothApproximation.ScalarData)
    (J : ∀ i, StandardTerminalIto (C := RealL2) (E := ℝ) (F i) (μ i) H)
    (u₀ : RealL2) (S : ∀ i, SingleNativeHeatEquation.Data (F i) (μ i) H D (J i) u₀)
    (M : ∀ i, NativeScalarModel.Model (J i)) :
    ∀ i j, NativePathLawComparison.law H (μ i) (S i).value (S i).continuous =
      NativePathLawComparison.law H (μ j) (S j).value (S j).continuous :=
  GivenSingleNativeGlobalUniqueness.laws_eq Ω F μ H D J u₀ S
    (NativeSingleGlobalInputs.products Ω F μ H J M) hH
    (NativeSingleGlobalInputs.inputs Ω F μ H D J u₀ S M hH)

end SHEStochastic.NativeGlobalUniqueness
