module

public import SHE.DampedKernelModel

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.DampedStochasticConvolution
open MeasureTheory Set Filter PredictableL2 HaarKernelApproximation HaarKernelL2Approximation
open scoped NNReal ENNReal Topology
local instance dampedStochasticConvolution_pFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance dampedStochasticConvolution_circleSigma : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance dampedStochasticConvolution_circleBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance dampedStochasticConvolution_columnsSigma : MeasurableSpace Columns := borel Columns
local instance dampedStochasticConvolution_columnsBorel : BorelSpace Columns := ⟨rfl⟩
local instance dampedStochasticConvolution_stateSigma : MeasurableSpace LowBands.StateL2 := borel LowBands.StateL2
local instance dampedStochasticConvolution_stateBorel : BorelSpace LowBands.StateL2 := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The constructed exponentially damped stochastic convolution, as an
actual complete predictable L² process for every bounded elliptic field. -/
def convolution (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0) (hh : (h:ℝ) ≤ 1)
    {Λ ell M : ℝ} (hΛ : 0 ≤ Λ) (hell : 0 < ell) (hM : 0 ≤ M)
    (I : StandardTerminalIto (C := Columns) (E := LowBands.StateL2) 𝓕 μ h)
    (f : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f) :
    Process (E := LowBands.StateL2) 𝓕 μ h :=
  KernelItoLimit.convolution (DampedKernelModel.model 𝓕 μ h hh hΛ hell hM) I ⟨f,hf⟩

theorem kernel_difference_norm_sq {Λ ell M t : ℝ} (hell : 0 < ell)
    (f g : FiniteHaar.EllipticField ell M) :
    ‖DampedHeatKernel.kernel Λ ell M hell (t,f)-DampedHeatKernel.kernel Λ ell M hell (t,g)‖^2=
      Real.exp (-2*Λ*t)*‖RealHaarIntegrand.kernel ell M hell (t,f)-RealHaarIntegrand.kernel ell M hell (t,g)‖^2 := by
  rw [DampedHeatKernel.kernel,DampedHeatKernel.kernel,← smul_sub,norm_smul,
    Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),mul_pow]
  have he : Real.exp (-Λ*t)^2=Real.exp (-2*Λ*t) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  rw [he]

theorem causal_pair_lintegral {Λ ell M : ℝ} (hell : 0 < ell) (μ : Measure Ω)
    (f g : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M) {h t : ℝ≥0} (ht : t ≤ h) :
    (∫⁻ s,∫⁻ ω,ENNReal.ofReal (‖DampedKernelModel.raw (Λ := Λ) hell f (t,(s,ω))-
      DampedKernelModel.raw (Λ := Λ) hell g (t,(s,ω))‖^2) ∂μ ∂timeMeasure h)=
      ∫⁻ s,∫⁻ ω,ENNReal.ofReal (‖DampedKernelModel.raw (Λ := Λ) hell f (t,(s,ω))-
        DampedKernelModel.raw (Λ := Λ) hell g (t,(s,ω))‖^2) ∂μ ∂timeMeasure t := by
  rw [← timeMeasure_restrict ht,← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr_ae
  filter_upwards [timeMeasure_ae_mem h] with s hs
  by_cases hst : s ≤ t
  · rw [Set.indicator_of_mem (show s ∈ Ioc 0 t from ⟨hs.1,hst⟩)]
  · rw [Set.indicator_of_notMem (show s ∉ Ioc 0 t from fun hh => hst hh.2)]
    have hτ : (t:ℝ)-(s:ℝ) ≤ 0 := sub_nonpos.mpr (by exact_mod_cast (le_of_not_ge hst))
    simp only [DampedKernelModel.raw,DampedHeatKernel.kernel_zero hell hτ,sub_self,norm_zero,
      zero_pow (by norm_num : (2:ℕ) ≠ 0),ENNReal.ofReal_zero,lintegral_zero]

theorem difference_causal_isometry (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0) (hh : (h:ℝ) ≤ 1)
    {Λ ell M : ℝ} (hΛ : 0 ≤ Λ) (hell : 0 < ell) (hM : 0 ≤ M)
    (I : StandardTerminalIto (C := Columns) (E := LowBands.StateL2) 𝓕 μ h)
    (f g : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M)
    (hf : StronglyMeasurable[𝓕.predictable] f) (hg : StronglyMeasurable[𝓕.predictable] g) :
    ENNReal.ofReal (‖convolution 𝓕 μ h hh hΛ hell hM I f hf-
      convolution 𝓕 μ h hh hΛ hell hM I g hg‖^2)=
      ∫⁻ t,∫⁻ s,∫⁻ ω,ENNReal.ofReal (Real.exp (-2*Λ*((t:ℝ)-(s:ℝ)))*
        ‖RealHaarIntegrand.kernel ell M hell ((t:ℝ)-(s:ℝ),f (s,ω))-
          RealHaarIntegrand.kernel ell M hell ((t:ℝ)-(s:ℝ),g (s,ω))‖^2)
        ∂μ ∂timeMeasure t ∂timeMeasure h := by
  have he := KernelItoLimit.difference_isometry (DampedKernelModel.model 𝓕 μ h hh hΛ hell hM) I
    (⟨f,hf⟩ : DampedKernelModel.Fields 𝓕 ell M) (⟨g,hg⟩ : DampedKernelModel.Fields 𝓕 ell M)
  rw [convolution,convolution,he]
  change (∫⁻ p,ENNReal.ofReal (‖DampedKernelModel.raw (Λ := Λ) hell f p-
    DampedKernelModel.raw (Λ := Λ) hell g p‖^2) ∂measure μ h)=_
  have hm : Measurable (fun p => ENNReal.ofReal (‖DampedKernelModel.raw (Λ := Λ) hell f p-
      DampedKernelModel.raw (Λ := Λ) hell g p‖^2)) :=
    ENNReal.continuous_ofReal.measurable.comp
      (((DampedKernelModel.raw_measurable hell (hf.mono (predictable_le_product 𝓕)).measurable).sub
        (DampedKernelModel.raw_measurable hell (hg.mono (predictable_le_product 𝓕)).measurable)).norm.pow_const 2)
  rw [triple_lintegral μ h hm]
  apply lintegral_congr_ae
  filter_upwards [timeMeasure_ae_mem h] with t ht
  rw [causal_pair_lintegral hell μ f g ht.2]
  apply lintegral_congr
  intro s
  apply lintegral_congr
  intro ω
  rw [DampedKernelModel.raw,DampedKernelModel.raw,kernel_difference_norm_sq]

end SHE.DampedStochasticConvolution
