module

public import SHE.PredictableL2
public import SHE.CompanionHeat

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace SHE.PredictableL2
open MeasureTheory Set
open scoped ENNReal NNReal InnerProductSpace

theorem realLp_norm_sq {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {μ : Measure X} (v : Lp E 2 μ) :
    ‖v‖^2=∫ x,‖v x‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem subsigma_norm_sq {X E : Type*} {m m0 : MeasurableSpace X} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (μ : @Measure X m0) (hm : m ≤ m0) (v : SubspaceLp (E := E) μ hm) :
    ‖v‖^2=∫ x,‖v x‖^2 ∂μ := by
  have hn := @realLp_norm_sq X E m _ _ (μ.trim hm) v
  rw [hn]
  have hs : StronglyMeasurable[m] (fun x => ‖v x‖^2) := by
    have hh := (Lp.stronglyMeasurable v).norm.pow 2
    change StronglyMeasurable[m] (fun x => ‖v x‖^2) at hh
    exact hh
  exact (integral_trim (μ := μ) hm hs).symm

section Process
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ] (h : ℝ≥0)

theorem process_integral_energy (v : Process (E := E) 𝓕 μ h) :
    ‖v‖^2=∫ t,∫ ω,‖v (t,ω)‖^2 ∂μ ∂timeMeasure h := by
  have hm := memLp_of_memLp_trim (predictable_le_product 𝓕) (Lp.memLp v)
  rw [subsigma_norm_sq]
  change (∫ p,‖v p‖^2 ∂(timeMeasure h).prod μ)=_
  exact integral_prod _ hm.norm.integrable_sq

theorem process_lintegral_energy (v : Process (E := E) 𝓕 μ h) :
    ENNReal.ofReal (‖v‖^2)=∫⁻ t,∫⁻ ω,ENNReal.ofReal (‖v (t,ω)‖^2) ∂μ ∂timeMeasure h := by
  have hm := memLp_of_memLp_trim (predictable_le_product 𝓕) (Lp.memLp v)
  rw [subsigma_norm_sq,ofReal_integral_eq_lintegral_ofReal hm.norm.integrable_sq
    (ae_of_all _ (fun _ => sq_nonneg _))]
  change (∫⁻ p,ENNReal.ofReal (‖v p‖^2) ∂(timeMeasure h).prod μ)=_
  apply lintegral_prod
  exact (ENNReal.continuous_ofReal.comp_aestronglyMeasurable
    (hm.aestronglyMeasurable.norm.pow 2)).aemeasurable

theorem process_difference_lintegral_energy (v w : Process (E := E) 𝓕 μ h) :
    ENNReal.ofReal (‖v-w‖^2)=∫⁻ t,∫⁻ ω,ENNReal.ofReal (‖v (t,ω)-w (t,ω)‖^2) ∂μ ∂timeMeasure h := by
  rw [process_lintegral_energy]
  apply lintegral_congr_ae
  have hh : ∀ᵐ p ∂energyMeasure μ h,(v-w) p=v p-w p :=
    ae_eq_of_ae_eq_trim (Lp.coeFn_sub v w)
  have hs := (Measure.ae_ae_of_ae_prod hh)
  filter_upwards [hs] with t ht
  apply lintegral_congr_ae
  filter_upwards [ht] with ω hω
  rw [hω]

end Process
end SHE.PredictableL2
