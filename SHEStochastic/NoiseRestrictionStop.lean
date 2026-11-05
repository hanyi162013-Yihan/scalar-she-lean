module

public import SHEStochastic.NoiseRestrictionBounds
public import SHEStochastic.StoppedSquareZero

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NoiseRestrictionStop
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω A C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (H T : ℝ≥0) (r : A →ₗᵢ[ℝ] C) (u : Process (E := A) F μ H)

/-- A fixed spatial isometry commutes with deterministic stopping of a
predictable cylindrical input. -/
theorem commutes :
    NoiseRestrictionBounds.input r (StoppedItoInputs.stop F μ H T u) =
      StoppedItoInputs.stop F μ H T (NoiseRestrictionBounds.input r u) := by
  apply PastItoAlgebra.eq_of_ambient_ae F μ H
  filter_upwards [ae_eq_of_ae_eq_trim (NoiseRestrictionBounds.input_ae_trim r
      (StoppedItoInputs.stop F μ H T u)),
    StoppedItoInputs.stop_ae F μ H T u,
    StoppedItoInputs.stop_ae F μ H T (NoiseRestrictionBounds.input r u),
    ae_eq_of_ae_eq_trim (NoiseRestrictionBounds.input_ae_trim r u)]
    with p hleft hu hright hr
  rw [hleft,hu,hright]
  by_cases hp : p ∈ StoppedItoInputs.before (Ω := Ω) T
  · rw [Set.indicator_of_mem hp,Set.indicator_of_mem hp,hr]
  · rw [Set.indicator_of_notMem hp,Set.indicator_of_notMem hp,map_zero]

end SHEStochastic.NoiseRestrictionStop
