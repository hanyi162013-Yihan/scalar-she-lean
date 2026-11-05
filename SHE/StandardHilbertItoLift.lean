module
public import SHE.HilbertColumnMap
public import SHE.OrthogonalItoChannels
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE
open MeasureTheory PredictableL2 OrthogonalItoChannels
open scoped NNReal ENNReal

/-- Ordinary Hilbert-valued integration for the SAME cylindrical Itô
map, on two orthogonal countable noise channels. This is a standard
stochastic input interface, not an internally proved construction.

In the Girsanov package it is used only under the changed probability.
Every scalar projection is explicitly tied to the same changed scalar
integral. No heat operator, coefficient, solution, law, or comparison
estimate occurs in this interface. -/
def StandardHilbertItoLift {Ω C : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup C] [InnerProductSpace ℝ C]
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} {H : ℝ≥0}
    (K : StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H) : Prop :=
  ∀ (ι E : Type) [Countable ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [SecondCountableTopology E]
    (e : Both (HilbertColumns.Space ι ℝ) →ₗᵢ[ℝ] C),
    ∃ (I₀ I₁ : StandardTerminalIto (C:=HilbertColumns.Space ι E) (E:=E) 𝓕 μ H),
      (∀ (L:E→L[ℝ] ℝ) (v:Process (E:=HilbertColumns.Space ι E) 𝓕 μ H),
        (L.compLpL 2 μ) (I₀.integral v)=K.integral
          (((e.toContinuousLinearMap.comp (left (C:=HilbertColumns.Space ι ℝ)).toContinuousLinearMap).comp
            (HilbertColumns.mapCLM L)).compLpL 2
              ((energyMeasure μ H).trim (predictable_le_product 𝓕)) v)) ∧
      (∀ (L:E→L[ℝ] ℝ) (v:Process (E:=HilbertColumns.Space ι E) 𝓕 μ H),
        (L.compLpL 2 μ) (I₁.integral v)=K.integral
          (((e.toContinuousLinearMap.comp (right (C:=HilbertColumns.Space ι ℝ)).toContinuousLinearMap).comp
            (HilbertColumns.mapCLM L)).compLpL 2
              ((energyMeasure μ H).trim (predictable_le_product 𝓕)) v))

end SHE
