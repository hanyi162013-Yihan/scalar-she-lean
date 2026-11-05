module

public import SHE.FixedHaarIntegral

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.TerminalHaarConvolution
open MeasureTheory Set PredictableL2 CircleHeat FiniteHaar
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (h : ℝ≥0) (hh : (h:ℝ) ≤ 1) {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
variable (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
variable (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := LowBands.StateL2) 𝓕 μ h)

/-- Actual fixed-terminal stochastic convolution, defined at EVERY time
of the interval as a genuine L² random variable. -/
def value (t : ℝ≥0) (ht : t ≤ h) : Lp LowBands.StateL2 2 μ :=
  I.integral (FixedHaarIntegral.input 𝓕 μ h hh hell hM f hf t ht)

theorem adapted_version (t : ℝ≥0) (ht : t ≤ h) :
    ∃ Z : Ω → LowBands.StateL2,StronglyMeasurable[𝓕 t] Z ∧
      value 𝓕 μ h hh hell hM f hf I t ht =ᵐ[μ] Z :=
  I.adapted t _ (FixedHaarIntegral.input_stopped 𝓕 μ h hh hell hM f hf t ht)

theorem centered (t : ℝ≥0) (ht : t ≤ h) :
    (∫ ω,value 𝓕 μ h hh hell hM f hf I t ht ω ∂μ)=0 := I.centered _

theorem difference_energy (t s : ℝ≥0) (ht : t ≤ h) (hs : s ≤ h) :
    ENNReal.ofReal (‖value 𝓕 μ h hh hell hM f hf I t ht-value 𝓕 μ h hh hell hM f hf I s hs‖^2)=
      ∫⁻ r,∫⁻ ω,ENNReal.ofReal (‖RealHaarIntegrand.kernel ell M hell ((t:ℝ)-(r:ℝ),f (r,ω))-
        RealHaarIntegrand.kernel ell M hell ((s:ℝ)-(r:ℝ),f (r,ω))‖^2) ∂μ ∂timeMeasure h := by
  rw [value,value,I.difference_energy]
  apply lintegral_congr_ae
  filter_upwards [Measure.ae_ae_of_ae_prod (FixedHaarIntegral.input_ae 𝓕 μ h hh hell hM f hf t ht),
    Measure.ae_ae_of_ae_prod (FixedHaarIntegral.input_ae 𝓕 μ h hh hell hM f hf s hs)] with r hr hr'
  apply lintegral_congr_ae
  filter_upwards [hr,hr'] with ω hω hω'
  rw [hω,hω']
  rfl

theorem value_zero : value 𝓕 μ h hh hell hM f hf I 0 (show (0:ℝ≥0) ≤ h from zero_le)=0 := by
  have hi : FixedHaarIntegral.input 𝓕 μ h hh hell hM f hf 0 (show (0:ℝ≥0) ≤ h from zero_le)=0 := by
    apply Lp.ext
    filter_upwards [(FixedHaarIntegral.kernel_memLp 𝓕 μ h hh hell hM hf 0 (show (0:ℝ≥0) ≤ h from zero_le)).coeFn_toLp,
      Lp.coeFn_zero RealHaarIntegrand.Columns 2 ((energyMeasure μ h).trim (predictable_le_product 𝓕))] with p hp hz
    unfold FixedHaarIntegral.input
    rw [hp,hz,FixedHaarIntegral.kernel,HaarKernelApproximation.kernel_zero hell
      (by simp only [NNReal.coe_zero,zero_sub,neg_nonpos]; exact p.1.2)]
    rfl
  rw [value,hi,map_zero]

end SHE.TerminalHaarConvolution
