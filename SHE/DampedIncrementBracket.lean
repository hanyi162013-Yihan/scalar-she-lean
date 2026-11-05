module

public import SHE.DampedFixedIntegral
public import SHE.DampedIncrementEnergy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.DampedIncrementBracket
open MeasureTheory Set PredictableL2 CircleHeat FiniteHaar
open scoped NNReal ENNReal
local instance : MeasurableSpace CircleL2 := borel CircleL2
local instance : BorelSpace CircleL2 := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Pathwise bracket control for the ACTUAL difference of two stopped
predictable heat integrands. The common full coefficient field is kept
inside both kernels. -/
theorem bracket_bound (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0) (hh : (h:ℝ) ≤ 1)
    {Λ ell M : ℝ} (hΛ : 0 ≤ Λ) (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    (s t : ℝ≥0) (hst : s ≤ t) (hth : t ≤ h) :
    ∀ᵐ ω ∂μ,(∫⁻ r,ENNReal.ofReal
      (‖(DampedFixedIntegral.input 𝓕 μ h hh hΛ hell hM f hf t hth-
        DampedFixedIntegral.input 𝓕 μ h hh hΛ hell hM f hf s (hst.trans hth) :
          Process (E := RealHaarIntegrand.Columns) 𝓕 μ h) (r,ω)‖^2) ∂timeMeasure h) ≤
      ENNReal.ofReal (DampedIncrementEnergy.incrementConstant Λ M*((t:ℝ)-(s:ℝ))^(1/4:ℝ)) := by
  have he : ∀ᵐ p ∂energyMeasure μ h,
      (DampedFixedIntegral.input 𝓕 μ h hh hΛ hell hM f hf t hth-
        DampedFixedIntegral.input 𝓕 μ h hh hΛ hell hM f hf s (hst.trans hth)) p=
      DampedHeatKernel.kernel Λ ell M hell ((t:ℝ)-(p.1:ℝ),f p)-
        DampedHeatKernel.kernel Λ ell M hell ((s:ℝ)-(p.1:ℝ),f p) := by
    filter_upwards [DampedFixedIntegral.input_ae 𝓕 μ h hh hΛ hell hM f hf t hth,
      DampedFixedIntegral.input_ae 𝓕 μ h hh hΛ hell hM f hf s (hst.trans hth),
      ae_eq_of_ae_eq_trim (Lp.coeFn_sub
        (DampedFixedIntegral.input 𝓕 μ h hh hΛ hell hM f hf t hth)
        (DampedFixedIntegral.input 𝓕 μ h hh hΛ hell hM f hf s (hst.trans hth)))] with p ht hs hp
    rw [hp]
    change DampedFixedIntegral.input 𝓕 μ h hh hΛ hell hM f hf t hth p-
      DampedFixedIntegral.input 𝓕 μ h hh hΛ hell hM f hf s (hst.trans hth) p=_
    rw [ht,hs]
    rfl
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure h)).quasiMeasurePreserving.ae he
  have hae := Measure.ae_ae_of_ae_prod hswap
  filter_upwards [hae] with ω hω
  calc
    _ = ∫⁻ r,DampedIncrementEnergy.energy (Λ := Λ) hell (fun r => f (r,ω)) s t r ∂timeMeasure h := by
      apply lintegral_congr_ae
      filter_upwards [hω] with r hr
      dsimp only [Prod.swap] at hr
      rw [hr]
      rfl
    _ ≤ _ := DampedIncrementEnergy.total_increment_energy hΛ hell hM hh hst hth (fun r => f (r,ω))
      (((hf.mono (predictable_le_product 𝓕)).measurable).comp (measurable_id.prodMk measurable_const))

end SHE.DampedIncrementBracket
