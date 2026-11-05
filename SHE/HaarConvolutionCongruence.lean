module
public import SHE.HaarConvolutionCausal
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.HaarStochasticConvolution
open MeasureTheory Set PredictableL2
open scoped NNReal ENNReal
variable {Ω:Type*}[MeasurableSpace Ω]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ]
variable(H:ℝ≥0)(hH:(H:ℝ)≤1){ell M:ℝ}(hell:0<ell)(hM:0≤M)
variable(I:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=LowBands.StateL2) 𝓕 μ H)

include hH in
theorem convolution_congr_ae(f g:ℝ≥0×Ω→FiniteHaar.EllipticField ell M)
    (hf:StronglyMeasurable[𝓕.predictable] f)(hg:StronglyMeasurable[𝓕.predictable] g)
    (he:f=ᵐ[energyMeasure μ H] g):
    convolution 𝓕 μ H hell hM I f hf=convolution 𝓕 μ H hell hM I g hg:=by
  have hh:=difference_causal_isometry 𝓕 μ H hH hell hM I f g hf hg
  have hs:=Measure.ae_ae_of_ae_prod he
  have hz:(∫⁻t,∫⁻s,∫⁻ω,ENNReal.ofReal
      (‖RealHaarIntegrand.kernel ell M hell ((t:ℝ)-(s:ℝ),f (s,ω))-
        RealHaarIntegrand.kernel ell M hell ((t:ℝ)-(s:ℝ),g (s,ω))‖^2)
      ∂μ ∂timeMeasure t ∂timeMeasure H)=0:=by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [timeMeasure_ae_mem H] with t ht
    apply lintegral_eq_zero_of_ae_eq_zero
    have hm:timeMeasure t≤timeMeasure H:=by
      rw [←timeMeasure_restrict ht.2]
      exact Measure.restrict_le_self
    filter_upwards [ae_mono hm hs] with s hse
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hse] with ω hω
    simp only [hω,sub_self,norm_zero,zero_pow (by decide:2≠0),ENNReal.ofReal_zero,Pi.zero_apply]
  rw [hz] at hh
  have hn:‖convolution 𝓕 μ H hell hM I f hf-convolution 𝓕 μ H hell hM I g hg‖=0:=by
    have hsq:=ENNReal.ofReal_eq_zero.mp hh
    nlinarith [norm_nonneg (convolution 𝓕 μ H hell hM I f hf-convolution 𝓕 μ H hell hM I g hg)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)
end SHE.HaarStochasticConvolution
