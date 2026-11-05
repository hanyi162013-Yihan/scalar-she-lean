module

public import SHE.FiniteItoCovarianceBounds

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.PredictableRealSections
open Set MeasureTheory PredictableL2
open scoped NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ] (H : ℝ≥0)

/-- A SINGLE original predictable-space event transfers to the actual
real sample/time window. No uncountable parameter event is substituted. -/
theorem of_energy_ae {P : ℝ≥0×Ω→Prop} (h : ∀ᵐ p∂energyMeasure μ H,P p)
    (a c : ℝ) (ha : 0≤a) (hac : a≤c) (hcH : c≤(H:ℝ)) :
    ∀ᵐ ω∂μ,∀ᵐ t:ℝ∂volume.restrict (Ioc a c),P (t.toNNReal,ω) := by
  have hs:=(Measure.measurePreserving_swap (μ:=μ) (ν:=timeMeasure H)).quasiMeasurePreserving.ae h
  have hr : ∀ᵐ ω∂μ,∀ᵐ t:ℝ∂volume.restrict (Ioc (0:ℝ) (H:ℝ)),P (t.toNNReal,ω) := by
    filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
    rw [←timeMeasure_map H]
    apply nonnegative_coe_measurableEmbedding.ae_map_iff.mpr
    simpa only [Real.toNNReal_coe,Prod.swap] using hω
  filter_upwards [hr] with ω hω
  exact hω.filter_mono (ae_mono (Measure.restrict_mono_set volume
    (show Ioc a c⊆Ioc (0:ℝ) (H:ℝ) from fun _ ht=>⟨ha.trans_lt ht.1,ht.2.trans hcH⟩)))

end SHE.PredictableRealSections
