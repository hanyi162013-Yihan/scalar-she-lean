module

public import SHEStochastic.ProductBrownianFamily
public import SHEStochastic.ProductHilbertBasis
public import SHEStochastic.StandardBrownianItoConstruction

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic.NativeProductIto
open MeasureTheory SHE SHE.OrthogonalItoChannels
open scoped NNReal
variable {Ω Ξ ι C : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
  [Countable ι] [DecidableEq ι] [Inhabited ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {G : Filtration ℝ≥0 ‹MeasurableSpace Ξ›} {H : ℝ≥0}
  (P : FiniteScalarIto.Family F μ H ι) (Q : FiniteScalarIto.Family G ν H ι)
  (e : HilbertBasis ι ℝ C)

/-- A genuine two-channel integral on the completed independent product.
Compatibility for every pulled-back L2 input is assembled separately. -/
def terminalIto : StandardTerminalIto (C := Both C) (E := ℝ)
    (IndependentNoiseCompletion.filtration μ ν F G) (IndependentNoiseCompletion.measure μ ν) H :=
  FiniteCylindricalIto.terminalIto (ProductBrownianFiniteLaw.family P Q).toCoordinates (ProductHilbertBasis.basis e)

theorem pastLocality : StandardTerminalPastLocality (terminalIto P Q e) :=
  FiniteCylindricalIto.pastLocality _ _

theorem hilbertLift : StandardHilbertItoLift (terminalIto P Q e) := standardHilbertItoLift _

theorem stoppedParameterFubini : StandardItoStoppedParameterFubini (terminalIto P Q e) :=
  FiniteCylindricalIto.stoppedParameterFubini _ _

end SHEStochastic.NativeProductIto
