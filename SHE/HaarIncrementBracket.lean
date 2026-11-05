module

public import SHE.FixedHaarIntegral
public import SHE.HaarIncrementEnergy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.HaarIncrementBracket
open MeasureTheory Set PredictableL2 CircleHeat FiniteHaar
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Pathwise bracket control for the ACTUAL difference of two stopped
predictable heat integrands. The common full coefficient field is kept
inside both kernels. -/
theorem bracket_bound (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0) (hh : (h:ℝ) ≤ 1)
    {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    (s t : ℝ≥0) (hst : s ≤ t) (hth : t ≤ h) :
    ∀ᵐ ω ∂μ,(∫⁻ r,ENNReal.ofReal
      (‖(FixedHaarIntegral.input 𝓕 μ h hh hell hM f hf t hth-
        FixedHaarIntegral.input 𝓕 μ h hh hell hM f hf s (hst.trans hth) :
          Process (E := RealHaarIntegrand.Columns) 𝓕 μ h) (r,ω)‖^2) ∂timeMeasure h) ≤
      ENNReal.ofReal (HaarIncrementEnergy.incrementConstant M*((t:ℝ)-(s:ℝ))^(1/4:ℝ)) := by
  have he : ∀ᵐ p ∂energyMeasure μ h,
      (FixedHaarIntegral.input 𝓕 μ h hh hell hM f hf t hth-
        FixedHaarIntegral.input 𝓕 μ h hh hell hM f hf s (hst.trans hth)) p=
      RealHaarIntegrand.kernel ell M hell ((t:ℝ)-(p.1:ℝ),f p)-
        RealHaarIntegrand.kernel ell M hell ((s:ℝ)-(p.1:ℝ),f p) := by
    filter_upwards [FixedHaarIntegral.input_ae 𝓕 μ h hh hell hM f hf t hth,
      FixedHaarIntegral.input_ae 𝓕 μ h hh hell hM f hf s (hst.trans hth),
      ae_eq_of_ae_eq_trim (Lp.coeFn_sub
        (FixedHaarIntegral.input 𝓕 μ h hh hell hM f hf t hth)
        (FixedHaarIntegral.input 𝓕 μ h hh hell hM f hf s (hst.trans hth)))] with p ht hs hp
    rw [hp]
    change FixedHaarIntegral.input 𝓕 μ h hh hell hM f hf t hth p-
      FixedHaarIntegral.input 𝓕 μ h hh hell hM f hf s (hst.trans hth) p=_
    rw [ht,hs]
    rfl
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure h)).quasiMeasurePreserving.ae he
  have hae := Measure.ae_ae_of_ae_prod hswap
  filter_upwards [hae] with ω hω
  calc
    _ = ∫⁻ r,HaarIncrementEnergy.energy hell (fun r => f (r,ω)) s t r ∂timeMeasure h := by
      apply lintegral_congr_ae
      filter_upwards [hω] with r hr
      dsimp only [Prod.swap] at hr
      rw [hr]
      rfl
    _ ≤ _ := HaarIncrementEnergy.total_increment_energy hell hM hh hst hth (fun r => f (r,ω))

end SHE.HaarIncrementBracket
