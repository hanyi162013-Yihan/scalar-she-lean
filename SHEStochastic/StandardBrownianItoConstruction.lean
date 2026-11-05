module

public import SHEStochastic.FiniteCylindricalLocality
public import SHEStochastic.StandardHilbertItoLift
public import SHE.StandardBrownianItoConstruction

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic
open MeasureTheory SHE
open scoped NNReal

/-- The ENTIRE recognized-coordinate construction predicate from the
original formalization, including past locality, Hilbert lifting and exact
coordinate identities. Only the stated finite-horizon Brownian laws are
inputs; no stochastic-calculus package is assumed. -/
theorem standardBrownianItoConstruction
    {Ω C ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
    [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
    [Countable ι] [DecidableEq ι]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ℝ≥0) (e : HilbertBasis ι ℝ C) (W : ι → ℝ≥0 → Ω → ℝ) :
    StandardBrownianItoConstruction F μ H e W := by
  intro hc ha hl
  let P : FiniteScalarIto.Family F μ H ι := ⟨⟨W, ha, hl⟩, hc⟩
  exact ⟨FiniteCylindricalIto.terminalIto P.toCoordinates e, FiniteCylindricalIto.pastLocality P e,
    standardHilbertItoLift _, FiniteCylindricalIto.coordinate_integral P e⟩

end SHEStochastic
