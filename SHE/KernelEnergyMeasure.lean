module

public import SHE.HaarKernelL2Approximation

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace SHE.HaarKernelL2Approximation
open MeasureTheory Set PredictableL2
open scoped ENNReal NNReal

theorem triple_lintegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    (h : ℝ≥0) {F : ℝ≥0 × (ℝ≥0 × Ω) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p,F p ∂measure μ h)=∫⁻ t,∫⁻ s,∫⁻ ω,F (t,(s,ω)) ∂μ ∂timeMeasure h ∂timeMeasure h := by
  change (∫⁻ p,F p ∂(timeMeasure h).prod ((timeMeasure h).prod μ))=_
  rw [lintegral_prod _ hF.aemeasurable]
  apply lintegral_congr
  intro t
  have hm : Measurable (fun p : ℝ≥0 × Ω => F (t,p)) :=
    hF.comp (measurable_const.prodMk measurable_id)
  exact lintegral_prod _ hm.aemeasurable

end SHE.HaarKernelL2Approximation
