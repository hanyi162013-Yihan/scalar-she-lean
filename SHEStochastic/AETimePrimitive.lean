module

public import SHEStochastic.FiniteItoTimeCalculus

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic.AETimePrimitive
open MeasureTheory SHE.PredictableL2 Filter Set
open scoped NNReal

/-- One time-probability AE identity gives equality of every physical
real-time primitive on one common event. No new integrability premise
is needed to transport equality of Bochner integrals. -/
theorem interval_integrals_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0) (q r : ℝ → Ω → ℝ)
    (he : ∀ᵐ p ∂energyMeasure μ H, q p.1 p.2 = r p.1 p.2) :
    ∀ᵐ ω ∂μ, ∀ T : ℝ≥0, T ≤ H →
      (∫ s in (0 : ℝ)..(T : ℝ), q s ω) = ∫ s in (0 : ℝ)..(T : ℝ), r s ω := by
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae he
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω T hT
  have hq : (∫ s, (Ioc (0 : ℝ≥0) T).indicator (fun s : ℝ≥0 ↦ q s ω) s ∂timeMeasure H) =
      ∫ s in (0 : ℝ)..(T : ℝ), q s ω := by
    rw [timeMeasure_eq]
    convert FiniteItoTimeCalculus.clock_cell H 0 T zero_le hT (fun s ↦ q s ω) using 1 <;> rfl
  have hr : (∫ s, (Ioc (0 : ℝ≥0) T).indicator (fun s : ℝ≥0 ↦ r s ω) s ∂timeMeasure H) =
      ∫ s in (0 : ℝ)..(T : ℝ), r s ω := by
    rw [timeMeasure_eq]
    convert FiniteItoTimeCalculus.clock_cell H 0 T zero_le hT (fun s ↦ r s ω) using 1 <;> rfl
  rw [← hq, ← hr]
  apply integral_congr_ae
  filter_upwards [hω] with s hs
  by_cases hst : s ∈ Ioc (0 : ℝ≥0) T
  · simp only [Set.indicator_of_mem hst]
    exact hs
  · simp only [Set.indicator_of_notMem hst]

end SHEStochastic.AETimePrimitive
