module

public import SHE.LpIntegralFubini
public import SHE.StandardTerminalIto

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.TerminalItoFubini
open MeasureTheory PredictableL2
open scoped NNReal ENNReal
variable {Ω P C E : Type*} [MeasurableSpace Ω] [MeasurableSpace P]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
variable (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ h)

/-- The original terminal Itô isometry commutes with parameter Bochner
integration. This is a theorem of the constructed common integral,
without a further stochastic Fubini axiom. -/
theorem integral_comm (ν : Measure P) (F : P→Process (E := C) 𝓕 μ h) :
    I.integral (∫ p,F p ∂ν)=∫ p,I.integral (F p) ∂ν :=
  (I.integral.integral_comp_comm F).symm

/-- Pointwise stochastic Fubini with every applicability condition
visible: an integrable predictable-L² family and a jointly integrable
version of its terminal integrals. The conclusion follows from ordinary
Bochner Fubini and the actual terminal Hilbert isometry. -/
theorem integral_ae (ν : Measure P) [SFinite ν]
    (F : P→Process (E := C) 𝓕 μ h) (hF : Integrable F ν)
    (H : P×Ω→E) (hH : Integrable H (ν.prod μ))
    (hRep : ∀ᵐ p ∂ν,I.integral (F p)=ᵐ[μ] fun ω => H (p,ω)) :
    I.integral (∫ p,F p ∂ν)=ᵐ[μ] fun ω => ∫ p,H (p,ω) ∂ν := by
  rw [integral_comm]
  exact LpIntegralFubini.integral_ae μ ν (fun p => I.integral (F p))
    (I.integral.toContinuousLinearMap.integrable_comp hF) H hH hRep

end SHE.TerminalItoFubini
