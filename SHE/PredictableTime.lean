module

public import SHE.PredictableL2
public import SHE.CompanionHeat

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace SHE.PredictableL2
open MeasureTheory Set
open scoped ENNReal NNReal

theorem timeMeasurePreserving (h : ℝ≥0) :
    MeasurePreserving ((↑) : ℝ≥0 → ℝ) (timeMeasure h) (volume.restrict (Ioc 0 (h:ℝ))) :=
  ⟨measurable_coe_nnreal_real,timeMeasure_map h⟩

theorem timeMeasure_lintegral (h : ℝ≥0) (f : ℝ≥0 → ℝ≥0∞) :
    (∫⁻ t,f t ∂timeMeasure h)=∫⁻ t in Ioc (0:ℝ) (h:ℝ),f t.toNNReal := by
  simpa only [Real.toNNReal_coe] using
    (timeMeasurePreserving h).lintegral_comp_emb nonnegative_coe_measurableEmbedding
      (fun t : ℝ => f t.toNNReal)

theorem timeMeasure_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ≥0) (f : ℝ≥0 → E) :
    (∫ t,f t ∂timeMeasure h)=∫ t in Ioc (0:ℝ) (h:ℝ),f t.toNNReal := by
  simpa only [Real.toNNReal_coe] using
    (timeMeasurePreserving h).integral_comp nonnegative_coe_measurableEmbedding
      (fun t : ℝ => f t.toNNReal)

theorem timeMeasure_ae_mem (h : ℝ≥0) : ∀ᵐ t ∂timeMeasure h,t ∈ Ioc 0 h := by
  have hh := (timeMeasurePreserving h).quasiMeasurePreserving.ae
    (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [hh] with t ht
  exact ⟨by exact_mod_cast ht.1,by exact_mod_cast ht.2⟩

instance timeMeasure_nullSingleton (h : ℝ≥0) : NullSingletonClass (timeMeasure h) where
  measure_singleton t := by
    rw [timeMeasure,nonnegative_coe_measurableEmbedding.comap_apply,Set.image_singleton]
    rw [Measure.restrict_apply (measurableSet_singleton (t:ℝ))]
    exact measure_mono_null inter_subset_left (by simp)

/-- Exact transfer of the square-root causal Volterra estimate to the
nonnegative physical time used by the predictable process space. -/
theorem predictable_picard_causal_energy (h : ℝ≥0) (F : ℝ≥0 → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ t,∫⁻ s,CompanionHeat.picardKernel (h:ℝ) ((t:ℝ)-(s:ℝ))*F s
      ∂timeMeasure t ∂timeMeasure h) ≤
      ENNReal.ofReal (2*(h:ℝ)^(1/2:ℝ))*(∫⁻ s,F s ∂timeMeasure h) := by
  have he : (∫⁻ t,∫⁻ s,CompanionHeat.picardKernel (h:ℝ) ((t:ℝ)-(s:ℝ))*F s
      ∂timeMeasure t ∂timeMeasure h)=
      ∫⁻ t in Ioc (0:ℝ) (h:ℝ),∫⁻ s in Ioc (0:ℝ) t,
        CompanionHeat.picardKernel (h:ℝ) (t-s)*F s.toNNReal := by
    rw [timeMeasure_lintegral]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [timeMeasure_lintegral,Real.coe_toNNReal _ ht.1.le]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [Real.coe_toNNReal _ hs.1.le]
  rw [he,timeMeasure_lintegral]
  exact CompanionHeat.picard_causal_energy h.2 _ (hF.comp measurable_real_toNNReal)

end SHE.PredictableL2
