module

public import SHE.TimeCausalPowers

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.PredictableL2
open MeasureTheory Set
open scoped NNReal ENNReal

def intervalTimeMeasure (s t : ℝ≥0) : Measure ℝ≥0 :=
  ((volume : Measure ℝ).restrict (Ioc (s:ℝ) (t:ℝ))).comap ((↑) : ℝ≥0 → ℝ)

instance intervalTimeMeasure_finite (s t : ℝ≥0) : IsFiniteMeasure (intervalTimeMeasure s t) := by
  unfold intervalTimeMeasure
  infer_instance

theorem timeMeasure_restrict_Ioc {h t : ℝ≥0} (s : ℝ≥0) (ht : t ≤ h) :
    (timeMeasure h).restrict (Ioc s t)=intervalTimeMeasure s t := by
  have hp : ((↑) : ℝ≥0 → ℝ) ⁻¹' Ioc (s:ℝ) (t:ℝ)=Ioc s t := by
    ext r
    simp only [mem_preimage,mem_Ioc,NNReal.coe_lt_coe,NNReal.coe_le_coe]
  change (((volume : Measure ℝ).restrict (Ioc (0:ℝ) (h:ℝ))).comap ((↑) : ℝ≥0 → ℝ)).restrict
    (Ioc s t)=_
  rw [← hp,← nonnegative_coe_measurableEmbedding.comap_restrict,Measure.restrict_restrict measurableSet_Ioc]
  rw [inter_eq_left.mpr (show Ioc (s:ℝ) (t:ℝ) ⊆ Ioc (0:ℝ) (h:ℝ) from
    fun _ hr => ⟨s.2.trans_lt hr.1,hr.2.trans (by exact_mod_cast ht)⟩)]
  rfl

theorem intervalTimeMeasure_map (s t : ℝ≥0) :
    (intervalTimeMeasure s t).map ((↑) : ℝ≥0 → ℝ)=
      (volume : Measure ℝ).restrict (Ioc (s:ℝ) (t:ℝ)) := by
  rw [intervalTimeMeasure,nonnegative_coe_measurableEmbedding.map_comap]
  have hr : range ((↑) : ℝ≥0 → ℝ)=Ici (0:ℝ) := by
    ext r
    constructor
    · rintro ⟨x,rfl⟩
      exact x.2
    · intro hx
      exact ⟨⟨r,hx⟩,rfl⟩
  rw [hr,Measure.restrict_restrict measurableSet_Ici]
  congr 1
  exact inter_eq_right.mpr (fun _ hx => (s.2.trans_lt hx.1).le)

theorem intervalTimeMeasure_lintegral (s t : ℝ≥0) (f : ℝ≥0 → ℝ≥0∞) :
    (∫⁻ r,f r ∂intervalTimeMeasure s t)=
      ∫⁻ r in Ioc (s:ℝ) (t:ℝ),f r.toNNReal := by
  have hm : MeasurePreserving ((↑) : ℝ≥0 → ℝ) (intervalTimeMeasure s t)
      (volume.restrict (Ioc (s:ℝ) (t:ℝ))) :=
    ⟨measurable_coe_nnreal_real,intervalTimeMeasure_map s t⟩
  simpa only [Real.toNNReal_coe] using hm.lintegral_comp_emb
    nonnegative_coe_measurableEmbedding (fun r : ℝ => f r.toNNReal)

theorem intervalTimeMeasure_ae_mem {h t : ℝ≥0} (s : ℝ≥0) (ht : t ≤ h) :
    ∀ᵐ r ∂intervalTimeMeasure s t,r ∈ Ioc s t := by
  rw [← timeMeasure_restrict_Ioc s ht]
  exact ae_restrict_mem measurableSet_Ioc

theorem interval_causal_rpow_mass {α : ℝ} (hα : -1 < α) {s t : ℝ≥0} (hst : s ≤ t) :
    (∫⁻ r,ENNReal.ofReal (((t:ℝ)-(r:ℝ))^α) ∂intervalTimeMeasure s t)=
      ENNReal.ofReal (((t:ℝ)-(s:ℝ))^(α+1)/(α+1)) := by
  rw [intervalTimeMeasure_lintegral]
  have he : (∫⁻ r in Ioc (s:ℝ) (t:ℝ),ENNReal.ofReal (((t:ℝ)-(r.toNNReal:ℝ))^α))=
      ∫⁻ r in Ioc (s:ℝ) (t:ℝ),ENNReal.ofReal (((t:ℝ)-r)^α) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [Real.coe_toNNReal _ (s.2.trans_lt hr.1).le]
  rw [he]
  have hst' : (s:ℝ) ≤ (t:ℝ) := by exact_mod_cast hst
  have hi : IntervalIntegrable (fun r : ℝ => r^α) volume 0 ((t:ℝ)-(s:ℝ)) :=
    intervalIntegral.intervalIntegrable_rpow' hα
  have ht : IntervalIntegrable (fun r : ℝ => ((t:ℝ)-r)^α) volume (s:ℝ) (t:ℝ) := by
    simpa only [sub_zero,sub_sub_cancel] using (hi.comp_sub_left (t:ℝ)).symm
  have hp : 0 ≤ᵐ[volume.restrict (Ioc (s:ℝ) (t:ℝ))] (fun r : ℝ => ((t:ℝ)-r)^α) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact Real.rpow_nonneg (sub_nonneg.mpr hr.2) α
  have ho := ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hst').mp ht) hp
  change ENNReal.ofReal (∫ r in Ioc (s:ℝ) (t:ℝ),((t:ℝ)-r)^α ∂volume)=
    ∫⁻ r in Ioc (s:ℝ) (t:ℝ),ENNReal.ofReal (((t:ℝ)-r)^α) ∂volume at ho
  have hioc : (∫ r in Ioc (s:ℝ) (t:ℝ),((t:ℝ)-r)^α ∂volume)=
      ∫ r in (s:ℝ)..(t:ℝ),((t:ℝ)-r)^α :=
    (intervalIntegral.integral_of_le (f := fun r : ℝ => ((t:ℝ)-r)^α) hst').symm
  have hswap : (∫ r in (s:ℝ)..(t:ℝ),((t:ℝ)-r)^α)=
      ∫ r in (0:ℝ)..((t:ℝ)-(s:ℝ)),r^α := by
    simpa only [sub_self] using
      intervalIntegral.integral_comp_sub_left (a := (s:ℝ)) (b := (t:ℝ)) (fun r : ℝ => r^α) (t:ℝ)
  rw [← ho,hioc,hswap,integral_rpow (Or.inl hα),Real.zero_rpow (by linarith : α+1 ≠ 0),sub_zero]

end SHE.PredictableL2
