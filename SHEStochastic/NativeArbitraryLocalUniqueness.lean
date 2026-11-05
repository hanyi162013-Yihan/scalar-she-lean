module

public import SHEStochastic.NativeSingleLocalInputs

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.NativeArbitraryLocalUniqueness
open MeasureTheory SHE SHE.DyadicApproximation SHE.FiniteHaar NativeScalarModel
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

/-- Ordinary inputs at the exact inverse-clock recast of the supplied native maps. -/
def inputs {ι : Type} [Fintype ι]
    (Ω : ι → Type) [∀ i, MeasurableSpace (Ω i)]
    (F : ∀ i, Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω i)))
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (H : ℝ≥0) (hH : 0<H) (hH1 : (H : ℝ)≤1)
    (D : SmoothApproximation.ScalarData)
    (J : ∀ i, StandardTerminalIto (C := RealL2) (E := ℝ) (F i) (μ i) H)
    (u₀ : RealL2) (U : ∀ i, SingleNativeHeatEquation.Data (F i) (μ i) H D (J i) u₀)
    (M : ∀ i, Model (J i)) :
    GivenSingleNativeArbitraryLocalUniqueness.Inputs Ω F μ H D J u₀ U := by
  let M' (i : ι) := recast (M i) (NativeInverseClock.filtration_eq (F i)) (NativeInverseClock.span_eq H)
    (NativeInverseClock.native (F i) (μ i) H (J i)) (NativeInverseClock.native_heq (F i) (μ i) H (J i))
  exact NativeSingleLocalInputs.inputs Ω (fun i ↦ NativeInverseClock.base (F i)) μ (NativeClock.time H) D
    (fun i ↦ NativeInverseClock.native (F i) (μ i) H (J i)) u₀
    (fun i ↦ NativeSingleLocalClock.model (μ i) (F i) H D (J i) u₀ (U i)) M'

/-- Bounded scalar local weak uniqueness with all seven ordinary
stochastic packages derived from the supplied native Brownian family. -/
theorem laws_eq {ι : Type} [Fintype ι]
    (Ω : ι → Type) [∀ i, MeasurableSpace (Ω i)]
    (F : ∀ i, Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω i)))
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (H : ℝ≥0) (hH : 0<H) (hH1 : (H : ℝ)≤1)
    (D : SmoothApproximation.ScalarData)
    (J : ∀ i, StandardTerminalIto (C := RealL2) (E := ℝ) (F i) (μ i) H)
    (u₀ : RealL2) (U : ∀ i, SingleNativeHeatEquation.Data (F i) (μ i) H D (J i) u₀)
    (M : ∀ i, Model (J i)) :
    ∀ i j, NativePathLawComparison.law H (μ i) (U i).value (U i).continuous =
      NativePathLawComparison.law H (μ j) (U j).value (U j).continuous := by
  exact GivenSingleNativeArbitraryLocalUniqueness.laws_eq Ω F μ H D J u₀ U hH hH1
    (inputs Ω F μ H hH hH1 D J u₀ U M)

end SHEStochastic.NativeArbitraryLocalUniqueness
