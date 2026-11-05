module

public import SHEStochastic.NativeFiniteItoInterval

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeFiniteIto
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal Topology

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

/-- Package 2 for the native cylindrical integral: the original universal
finite-dimensional Itô interface, with arbitrary predictable random L²
rows and the original gradient-row stochastic integral. -/
theorem standardFiniteIto (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C) :
    StandardFiniteIto.Universal F μ H (FiniteCylindricalIto.terminalIto P.toCoordinates e) := by
  constructor
  intro n R z Y hY hc hRep a b ha hab hb G dG hG
  have hb0 : 0 ≤ b := ha.trans hab
  have hab' : a.toNNReal ≤ b.toNNReal := Real.toNNReal_le_toNNReal hab
  have hb' : b.toNNReal ≤ H := by
    exact_mod_cast (show (b.toNNReal : ℝ) ≤ (H : ℝ) by rwa [Real.coe_toNNReal b hb0])
  have hG' : GaussianItoTest.RegularTest (a.toNNReal : ℝ) (b.toNNReal : ℝ) G dG := by
    simpa only [Real.coe_toNNReal a ha, Real.coe_toNNReal b hb0] using hG
  simpa only [Real.coe_toNNReal a ha, Real.coe_toNNReal b hb0] using
    NativeFiniteItoInterval.formula P e R z Y hY hc hRep a.toNNReal b.toNNReal hab' hb' G dG hG'

end SHEStochastic.NativeFiniteIto
