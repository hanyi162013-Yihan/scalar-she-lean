module

public import SHE.StoppedItoInputs
public import SHE.PredictableTime

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.StoppedBoundedBracket
open Set MeasureTheory PredictableL2 StoppedItoInputs
open scoped NNReal ENNReal

theorem time_interval_mass (H s t : ℝ≥0) :
    timeMeasure H (Ico s t)≤ENNReal.ofReal ((t:ℝ)-(s:ℝ)) := by
  have he : (((↑) : ℝ≥0 → ℝ) ⁻¹' Ico (s:ℝ) (t:ℝ))=Ico s t := by
    ext r
    simp only [mem_preimage,mem_Ico]
    exact_mod_cast (Iff.rfl : (s≤r ∧ r<t)↔(s≤r ∧ r<t))
  rw [←he,(timeMeasurePreserving H).measure_preimage measurableSet_Ico.nullMeasurableSet,
    Measure.restrict_apply measurableSet_Ico]
  exact (measure_mono inter_subset_left).trans_eq Real.volume_Ico

variable {Ω C : Type*} [MeasurableSpace Ω] [NormedAddCommGroup C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ] (H : ℝ≥0)

/-- A genuine uniformly bounded predictable row has a linearly small
pathwise bracket on every stopped time increment of the SAME integral. -/
theorem increment_bound (u : Process (E := C) 𝓕 μ H) {K : ℝ} (hK : 0≤K)
    (hu : ∀ᵐ p ∂energyMeasure μ H, ‖u p‖^2≤K)
    (s t : ℝ≥0) (hst : s≤t) :
    ∀ᵐ ω ∂μ, (∫⁻ r,ENNReal.ofReal
      (‖(stop 𝓕 μ H (t:ℝ) u-stop 𝓕 μ H (s:ℝ) u) (r,ω)‖^2) ∂timeMeasure H)≤
      ENNReal.ofReal (K*((t:ℝ)-(s:ℝ))) := by
  have he : ∀ᵐ p ∂energyMeasure μ H,
      ‖(stop 𝓕 μ H (t:ℝ) u-stop 𝓕 μ H (s:ℝ) u) p‖^2≤
        (Ico s t).indicator (fun _ => K) p.1 := by
    filter_upwards [hu,stop_ae 𝓕 μ H (t:ℝ) u,stop_ae 𝓕 μ H (s:ℝ) u,
      ae_eq_of_ae_eq_trim (Lp.coeFn_sub (stop 𝓕 μ H (t:ℝ) u) (stop 𝓕 μ H (s:ℝ) u))]
      with p hp ht hs he
    rw [he]
    simp only [Pi.sub_apply]
    rw [ht,hs]
    simp only [Set.indicator_apply,before,mem_setOf_eq]
    change ‖(if p.1<t then u p else 0)-(if p.1<s then u p else 0)‖^2≤
      (if p.1∈Ico s t then K else 0)
    by_cases hps : p.1<s
    · have hpt : p.1<t := hps.trans_le hst
      simp [hpt,hps,mem_Ico,not_le.mpr hps]
    · by_cases hpt : p.1<t
      · have hpm : p.1∈Ico s t := ⟨le_of_not_gt hps,hpt⟩
        simpa only [hpt,hps,ite_true,ite_false,sub_zero,hpm] using hp
      · simp [hpt,hps,mem_Ico]
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae he
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  calc
    _ ≤ ∫⁻ r,(Ico s t).indicator (fun _ => ENNReal.ofReal K) r ∂timeMeasure H := by
      apply lintegral_mono_ae
      filter_upwards [hω] with r hr
      have hh := ENNReal.ofReal_le_ofReal hr
      by_cases hrmem : r∈Ico s t <;> simpa [Prod.swap,hrmem] using hh
    _ = ENNReal.ofReal K*timeMeasure H (Ico s t) := by
      rw [lintegral_indicator measurableSet_Ico,lintegral_const,Measure.restrict_apply_univ,mul_comm]
    _ ≤ ENNReal.ofReal K*ENNReal.ofReal ((t:ℝ)-(s:ℝ)) :=
      mul_le_mul_right (time_interval_mass H s t) _
    _ = _ := (ENNReal.ofReal_mul hK).symm

end SHE.StoppedBoundedBracket
