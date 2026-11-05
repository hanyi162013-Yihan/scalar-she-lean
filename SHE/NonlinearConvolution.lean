module

public import SHE.HaarConvolutionCausal
public import SHE.CompanionPicard

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.NonlinearConvolution
open MeasureTheory Set PredictableL2 LowBands NonlinearHaarIntegrand
open scoped NNReal ENNReal
local instance nonlinearConvolution_pFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance nonlinearConvolution_circleSigma : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance nonlinearConvolution_circleBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance nonlinearConvolution_stateSigma : MeasurableSpace StateL2 := borel StateL2
local instance nonlinearConvolution_stateBorel : BorelSpace StateL2 := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
variable {a : ℝ → ℝ} (ha : Measurable a) {ell M H β : ℝ}
variable (hell : 0 < ell) (hb : ∀ z,ell ≤ a z ∧ a z ≤ M)
variable (hβ : 0 < β) (hH : 0 ≤ H) (hholder : ∀ z w,|a z-a w| ≤ H*|z-w|^β)

def field (u : Process (E := StateL2) 𝓕 μ h) : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M :=
  fun p => coefficientField a ha ell M hell hb (u p)

include hβ hH hholder in
omit [IsProbabilityMeasure μ] in
theorem field_predictable (u : Process (E := StateL2) 𝓕 μ h) :
    StronglyMeasurable[𝓕.predictable] (field 𝓕 μ h ha hell hb u) :=
  ((coefficientField_measurable ha hell hb hβ hH hholder).comp (Lp.stronglyMeasurable u).measurable).stronglyMeasurable

/-- The literal state-to-stochastic-convolution map, built from standard
terminal Itô integration and the actual nonlinear common-Haar factor. -/
def map (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) 𝓕 μ h)
    (u : Process (E := StateL2) 𝓕 μ h) : Process (E := StateL2) 𝓕 μ h :=
  HaarStochasticConvolution.convolution 𝓕 μ h hell
    (hell.le.trans ((hb 0).1.trans (hb 0).2)) I
    (field 𝓕 μ h ha hell hb u) (field_predictable 𝓕 μ h ha hell hb hβ hH hholder u)

/-- The formerly supplied companion isometry now holds for the
constructed nonlinear convolution, with no convolution premise. -/
theorem undamped_isometry (hh : (h:ℝ) ≤ 1)
    (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) 𝓕 μ h) :
    CompanionPicard.DampedConvolutionIsometry 𝓕 μ h a ha M (absBound hell hb) 0
      (map 𝓕 μ h ha hell hb hβ hH hholder I) := by
  intro u v
  rw [map,map,HaarStochasticConvolution.difference_causal_isometry 𝓕 μ h hh]
  apply lintegral_congr_ae
  filter_upwards [timeMeasure_ae_mem h] with t ht
  apply lintegral_congr_ae
  filter_upwards [timeMeasure_ae_mem t,(timeMeasure t).ae_ne t] with s hs hst
  have hst' : s < t := lt_of_le_of_ne hs.2 hst
  have hτ : 0 < (t:ℝ)-(s:ℝ) := sub_pos.mpr (by exact_mod_cast hst')
  apply lintegral_congr
  intro ω
  change ENNReal.ofReal (‖kernel a ha ell M hell hb ((t:ℝ)-(s:ℝ),u (s,ω))-
    kernel a ha ell M hell hb ((t:ℝ)-(s:ℝ),v (s,ω))‖^2)=_
  rw [kernel_difference_norm_sq ha hell hb hτ]
  simp only [zero_mul,mul_zero,Real.exp_zero,one_mul]

end SHE.NonlinearConvolution
