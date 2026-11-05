module

public import SHE.TerminalHaarConvolution

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.FixedHaarIntegral
open MeasureTheory Set PredictableL2 CircleHeat FiniteHaar
open scoped NNReal ENNReal
local instance haarIntegralCongruence_pFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance haarIntegralCongruence_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns := borel RealHaarIntegrand.Columns
local instance haarIntegralCongruence_columnsBorel : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (h : ℝ≥0) (hh : (h:ℝ) ≤ 1) {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
variable (f g : ℝ≥0 × Ω → EllipticField ell M)
variable (hf : StronglyMeasurable[𝓕.predictable] f) (hg : StronglyMeasurable[𝓕.predictable] g)

/-- Changing a coefficient field on a time/probability null set leaves
every actual fixed-terminal stochastic heat integrand unchanged. -/
theorem input_congr (hfg : f =ᵐ[energyMeasure μ h] g) (t : ℝ≥0) (ht : t ≤ h) :
    input 𝓕 μ h hh hell hM f hf t ht=input 𝓕 μ h hh hell hM g hg t ht := by
  apply Lp.ext
  apply ae_eq_trim_of_measurable (predictable_le_product 𝓕)
    (Lp.stronglyMeasurable _).measurable (Lp.stronglyMeasurable _).measurable
  filter_upwards [input_ae 𝓕 μ h hh hell hM f hf t ht,
    input_ae 𝓕 μ h hh hell hM g hg t ht,hfg] with p hp hq hfield
  rw [hp,hq,kernel,kernel,hfield]

theorem terminal_value_congr
    (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := LowBands.StateL2) 𝓕 μ h)
    (hfg : f =ᵐ[energyMeasure μ h] g) (t : ℝ≥0) (ht : t ≤ h) :
    TerminalHaarConvolution.value 𝓕 μ h hh hell hM f hf I t ht=
      TerminalHaarConvolution.value 𝓕 μ h hh hell hM g hg I t ht := by
  rw [TerminalHaarConvolution.value,TerminalHaarConvolution.value,
    input_congr 𝓕 μ h hh hell hM f g hf hg hfg t ht]

end SHE.FixedHaarIntegral
