module

public import SHE.HaarStochasticConvolution

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.HaarStochasticConvolution
open MeasureTheory Set Filter PredictableL2 HaarKernelApproximation HaarKernelL2Approximation
open scoped NNReal ENNReal Topology
local instance haarConvolutionCausal_pFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance haarConvolutionCausal_circleSigma : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance haarConvolutionCausal_circleBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance haarConvolutionCausal_columnsSigma : MeasurableSpace Columns := borel Columns
local instance haarConvolutionCausal_columnsBorel : BorelSpace Columns := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]

theorem causal_pair_lintegral {ell M : ℝ} (hell : 0 < ell) (μ : Measure Ω)
    (f g : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M) {h t : ℝ≥0} (ht : t ≤ h) :
    (∫⁻ s,∫⁻ ω,ENNReal.ofReal (‖raw hell f (t,(s,ω))-raw hell g (t,(s,ω))‖^2)
      ∂μ ∂timeMeasure h)=
      ∫⁻ s,∫⁻ ω,ENNReal.ofReal (‖raw hell f (t,(s,ω))-raw hell g (t,(s,ω))‖^2)
      ∂μ ∂timeMeasure t := by
  rw [← timeMeasure_restrict ht,← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr_ae
  filter_upwards [timeMeasure_ae_mem h] with s hs
  by_cases hst : s ≤ t
  · rw [Set.indicator_of_mem (show s ∈ Ioc 0 t from ⟨hs.1,hst⟩)]
  · rw [Set.indicator_of_notMem (show s ∉ Ioc 0 t from fun hh => hst hh.2)]
    have hτ : (t:ℝ)-(s:ℝ) ≤ 0 := sub_nonpos.mpr (by exact_mod_cast (le_of_not_ge hst))
    simp only [raw,kernel_zero hell hτ,sub_self,norm_zero,
      zero_pow (by norm_num : (2:ℕ) ≠ 0),ENNReal.ofReal_zero,lintegral_zero]

theorem difference_causal_isometry (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0) (hh : (h:ℝ) ≤ 1)
    {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    (I : StandardTerminalIto (C := Columns) (E := LowBands.StateL2) 𝓕 μ h)
    (f g : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M)
    (hf : StronglyMeasurable[𝓕.predictable] f) (hg : StronglyMeasurable[𝓕.predictable] g) :
    ENNReal.ofReal (‖convolution 𝓕 μ h hell hM I f hf-convolution 𝓕 μ h hell hM I g hg‖^2)=
      ∫⁻ t,∫⁻ s,∫⁻ ω,ENNReal.ofReal
        (‖RealHaarIntegrand.kernel ell M hell ((t:ℝ)-(s:ℝ),f (s,ω))-
          RealHaarIntegrand.kernel ell M hell ((t:ℝ)-(s:ℝ),g (s,ω))‖^2)
        ∂μ ∂timeMeasure t ∂timeMeasure h := by
  rw [difference_isometry 𝓕 μ h hell hM I hh f g hf hg]
  have hm : Measurable (fun p => ENNReal.ofReal (‖raw hell f p-raw hell g p‖^2)) :=
    ENNReal.continuous_ofReal.measurable.comp
      (((raw_measurable hell (hf.mono (predictable_le_product 𝓕)).measurable).sub
        (raw_measurable hell (hg.mono (predictable_le_product 𝓕)).measurable)).norm.pow_const 2)
  rw [triple_lintegral μ h hm]
  apply lintegral_congr_ae
  filter_upwards [timeMeasure_ae_mem h] with t ht
  rw [causal_pair_lintegral hell μ f g ht.2]
  rfl

end SHE.HaarStochasticConvolution
