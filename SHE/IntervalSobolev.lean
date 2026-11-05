module

public import SHE.FractionalHardy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.IntervalSobolev
open Finset Set MeasureTheory AddCircle CircleHeat CircleFractional FractionalHardy
open scoped ENNReal
local instance intervalSobolev_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

def shift (u : C(AddCircle (1:ℝ),ℂ)) (c : AddCircle (1:ℝ)) : C(AddCircle (1:ℝ),ℂ) :=
  ⟨fun x => u (x+c),by fun_prop⟩

def reflect (u : C(AddCircle (1:ℝ),ℂ)) : C(AddCircle (1:ℝ),ℂ) := ⟨fun x => u (-x),by fun_prop⟩

theorem square_shift (u : C(AddCircle (1:ℝ),ℂ)) (c : AddCircle (1:ℝ)) :
    circleSquare (shift u c) = circleSquare u := by
  change (∫ x, ‖u (x+c)‖^2 ∂haarAddCircle) = ∫ x, ‖u x‖^2 ∂haarAddCircle
  exact integral_add_right_eq_self (μ := haarAddCircle) (fun x : AddCircle (1:ℝ) => ‖u x‖^2) c

theorem square_reflect (u : C(AddCircle (1:ℝ),ℂ)) : circleSquare (reflect u) = circleSquare u := by
  change (∫ x, ‖u (-x)‖^2 ∂haarAddCircle) = ∫ x, ‖u x‖^2 ∂haarAddCircle
  exact integral_neg_eq_self (fun x : AddCircle (1:ℝ) => ‖u x‖^2) haarAddCircle

theorem translation_shift (u : C(AddCircle (1:ℝ),ℂ)) (c : AddCircle (1:ℝ)) (z : ℝ) :
    circleTranslationEnergy (shift u c) z = circleTranslationEnergy u z := by
  unfold circleTranslationEnergy
  have he := integral_add_right_eq_self (μ := haarAddCircle)
    (fun x : AddCircle (1:ℝ) => ‖u (x+(z : AddCircle (1:ℝ)))-u x‖^2) c
  convert he using 1
  apply integral_congr_ae
  filter_upwards with x
  change ‖u ((x+(z : AddCircle (1:ℝ)))+c)-u (x+c)‖^2 = ‖u ((x+c)+(z : AddCircle (1:ℝ)))-u (x+c)‖^2
  rw [show (x+(z : AddCircle (1:ℝ)))+c = (x+c)+(z : AddCircle (1:ℝ)) by abel]

theorem translation_reflect (u : C(AddCircle (1:ℝ),ℂ)) (z : ℝ) :
    circleTranslationEnergy (reflect u) z = circleTranslationEnergy u z := by
  unfold circleTranslationEnergy
  calc
    _ = ∫ x : AddCircle (1:ℝ), ‖u (x-(z : AddCircle (1:ℝ)))-u x‖^2 ∂haarAddCircle := by
      have he := integral_neg_eq_self
        (fun x : AddCircle (1:ℝ) => ‖u (x-(z : AddCircle (1:ℝ)))-u x‖^2) haarAddCircle
      convert he using 1
      apply integral_congr_ae
      filter_upwards with x
      change ‖u (-(x+(z : AddCircle (1:ℝ))))-u (-x)‖^2 = ‖u (-x-(z : AddCircle (1:ℝ)))-u (-x)‖^2
      simp only [neg_add,sub_eq_add_neg]
    _ = _ := by
      have he := integral_add_right_eq_self (μ := haarAddCircle)
        (fun x : AddCircle (1:ℝ) => ‖u (x-(z : AddCircle (1:ℝ)))-u x‖^2) (z : AddCircle (1:ℝ))
      rw [← he]
      apply integral_congr_ae
      filter_upwards with x
      rw [add_sub_cancel_right,norm_sub_rev]

theorem gagliardo_shift (ρ : ℝ) (u : C(AddCircle (1:ℝ),ℂ)) (c : AddCircle (1:ℝ)) :
    circleFractionalSq ρ (shift u c) = circleFractionalSq ρ u := by
  unfold circleFractionalSq
  simp only [translation_shift]

theorem gagliardo_reflect (ρ : ℝ) (u : C(AddCircle (1:ℝ),ℂ)) :
    circleFractionalSq ρ (reflect u) = circleFractionalSq ρ u := by
  unfold circleFractionalSq
  simp only [translation_reflect]

theorem exists_hardy_half_bound {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : C(AddCircle (1:ℝ),ℂ),
      IntegrableOn (fun z : ℝ => circleTranslationEnergy u z*z^(-1-2*ρ)) (Ioi 0) →
      hardy ρ (1/2) u ≤ C*(circleSquare u+circleFractionalSq ρ u) := by
  obtain ⟨C,hC,hbound⟩ := exists_hardy_bound hρ hρhalf
  let c : ℝ := (1/4:ℝ)^(-2*ρ)
  have hc : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨C+c,add_pos hC hc,?_⟩
  intro u hG
  have hb := hbound u hG
  have ht := hardy_tail_bound hρ hρhalf u
  have hm := hardy_mono hρhalf (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 3/4) u
  have hG0 := gagliardo_nonneg ρ u
  change hardy ρ (3/4) u ≤ hardy ρ (1/4) u+c*circleSquare u at ht
  nlinarith [mul_nonneg hc.le hG0]

def endpointDensity (ρ : ℝ) (u : C(AddCircle (1:ℝ),ℂ)) (x : AddCircle (1:ℝ)) : ℝ :=
  ‖x‖^(-2*ρ)*‖u x‖^2

theorem norm_coe_half {x : ℝ} (hx : x ∈ Icc (-(1/2:ℝ)) (1/2)) :
    ‖(x : AddCircle (1:ℝ))‖ = |x| := by
  apply (AddCircle.norm_coe_eq_abs_iff (1:ℝ) (by norm_num : (1:ℝ) ≠ 0)).mpr
  norm_num only [abs_one]
  exact abs_le.mpr hx

theorem endpoint_lift_pos (ρ : ℝ) (u : C(AddCircle (1:ℝ),ℂ)) {x : ℝ} (hx : x ∈ Icc (0:ℝ) (1/2)) :
    endpointDensity ρ u (x : AddCircle (1:ℝ)) = density ρ u x := by
  unfold endpointDensity density
  rw [norm_coe_half ⟨by linarith [hx.1],hx.2⟩,abs_of_nonneg hx.1]

theorem endpoint_lift_neg (ρ : ℝ) (u : C(AddCircle (1:ℝ),ℂ)) {x : ℝ} (hx : x ∈ Icc (-(1/2:ℝ)) 0) :
    endpointDensity ρ u (x : AddCircle (1:ℝ)) = density ρ (reflect u) (-x) := by
  unfold endpointDensity density
  rw [norm_coe_half ⟨hx.1,by linarith [hx.2]⟩,abs_of_nonpos hx.2]
  simp only [QuotientAddGroup.mk_neg,reflect,ContinuousMap.coe_mk,neg_neg]

theorem endpoint_integrable {ρ : ℝ} (hρhalf : ρ < 1/2) (u : C(AddCircle (1:ℝ),ℂ)) :
    Integrable (endpointDensity ρ u) haarAddCircle := by
  have hpos : IntervalIntegrable (fun x : ℝ => endpointDensity ρ u (x : AddCircle (1:ℝ))) volume 0 (1/2) := by
    apply (density_intervalIntegrable hρhalf (by norm_num : (0:ℝ) ≤ 1/2) u).congr
    intro x hx
    rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1/2)] at hx
    exact (endpoint_lift_pos ρ u ⟨hx.1.le,hx.2⟩).symm
  have hneg : IntervalIntegrable (fun x : ℝ => endpointDensity ρ u (x : AddCircle (1:ℝ))) volume (-(1/2)) 0 := by
    have hh := (IntervalIntegrable.iff_comp_neg).mp
      (density_intervalIntegrable hρhalf (by norm_num : (0:ℝ) ≤ 1/2) (reflect u))
    have hh' : IntervalIntegrable (fun x : ℝ => density ρ (reflect u) (-x)) volume (-(1/2)) 0 := by
      simpa only [neg_zero] using hh.symm
    apply hh'.congr
    intro x hx
    rw [uIoc_of_le (by norm_num : (-(1/2:ℝ)) ≤ 0)] at hx
    exact (endpoint_lift_neg ρ u ⟨hx.1.le,hx.2⟩).symm
  have hreal := ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (-(1/2:ℝ)) ≤ 1/2)).mp (hneg.trans hpos))
  have hv : (volume : Measure (AddCircle (1:ℝ))) = haarAddCircle := by
    simpa only [ENNReal.ofReal_one,one_smul] using AddCircle.volume_eq_smul_haarAddCircle (T := (1:ℝ))
  have hp := AddCircle.measurePreserving_mk (1:ℝ) (-(1/2:ℝ))
  rw [hv] at hp
  have hm : Measurable (endpointDensity ρ u) := by unfold endpointDensity; fun_prop
  apply (hp.integrable_comp hm.aestronglyMeasurable).mp
  simpa only [IntegrableOn,Function.comp_apply,show (-(1/2:ℝ))+1 = 1/2 by norm_num] using! hreal

theorem endpoint_integral_split (ρ : ℝ) (hρhalf : ρ < 1/2) (u : C(AddCircle (1:ℝ),ℂ)) :
    (∫ x, endpointDensity ρ u x ∂haarAddCircle) = hardy ρ (1/2) (reflect u)+hardy ρ (1/2) u := by
  have hv : (volume : Measure (AddCircle (1:ℝ))) = haarAddCircle := by
    simpa only [ENNReal.ofReal_one,one_smul] using AddCircle.volume_eq_smul_haarAddCircle (T := (1:ℝ))
  have hreal := (AddCircle.measurePreserving_mk (1:ℝ) (-(1/2:ℝ))).integrable_comp
    (by rw [hv]; exact (endpoint_integrable hρhalf u).aestronglyMeasurable)
  have hint : IntervalIntegrable (fun x : ℝ => endpointDensity ρ u (x : AddCircle (1:ℝ))) volume (-(1/2)) (1/2) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (-(1/2:ℝ)) ≤ 1/2)).mpr
    simpa only [IntegrableOn,Function.comp_apply,show (-(1/2:ℝ))+1 = 1/2 by norm_num] using! hreal.mpr (by rw [hv]; exact endpoint_integrable hρhalf u)
  have hneg : IntervalIntegrable (fun x : ℝ => endpointDensity ρ u (x : AddCircle (1:ℝ))) volume (-(1/2)) 0 :=
    hint.mono_set (by
      rw [Set.uIcc_of_le (by norm_num : (-(1/2:ℝ)) ≤ 0),Set.uIcc_of_le (by norm_num : (-(1/2:ℝ)) ≤ 1/2)]
      intro x hx
      exact ⟨hx.1,le_trans hx.2 (by norm_num)⟩)
  have hpos : IntervalIntegrable (fun x : ℝ => endpointDensity ρ u (x : AddCircle (1:ℝ))) volume 0 (1/2) :=
    hint.mono_set (by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/2),Set.uIcc_of_le (by norm_num : (-(1/2:ℝ)) ≤ 1/2)]
      intro x hx
      exact ⟨le_trans (by norm_num) hx.1,hx.2⟩)
  calc
    _ = ∫ x in (-(1/2:ℝ))..(1/2:ℝ), endpointDensity ρ u (x : AddCircle (1:ℝ)) := by
      rw [← hv]
      simpa only [show (-(1/2:ℝ))+1 = 1/2 by norm_num] using
        (AddCircle.intervalIntegral_preimage (1:ℝ) (-(1/2:ℝ)) (endpointDensity ρ u)).symm
    _ = (∫ x in (-(1/2:ℝ))..0, endpointDensity ρ u (x : AddCircle (1:ℝ)))+
        ∫ x in (0:ℝ)..(1/2:ℝ), endpointDensity ρ u (x : AddCircle (1:ℝ)) :=
      (intervalIntegral.integral_add_adjacent_intervals hneg hpos).symm
    _ = _ := by
      congr 1
      · calc
          _ = ∫ x in (-(1/2:ℝ))..0, density ρ (reflect u) (-x) := by
            apply intervalIntegral.integral_congr
            intro x hx
            rw [uIcc_of_le (by norm_num : (-(1/2:ℝ)) ≤ 0)] at hx
            exact endpoint_lift_neg ρ u hx
          _ = _ := by rw [intervalIntegral.integral_comp_neg]; simp only [neg_zero,neg_neg,hardy]
      · apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/2)] at hx
        exact endpoint_lift_pos ρ u hx

theorem exists_endpoint_bound {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : C(AddCircle (1:ℝ),ℂ),
      IntegrableOn (fun z : ℝ => circleTranslationEnergy u z*z^(-1-2*ρ)) (Ioi 0) →
      (∫ x, endpointDensity ρ u x ∂haarAddCircle) ≤ C*(circleSquare u+circleFractionalSq ρ u) := by
  obtain ⟨C,hC,hbound⟩ := exists_hardy_half_bound hρ hρhalf
  refine ⟨2*C,by positivity,?_⟩
  intro u hG
  have hGr : IntegrableOn (fun z : ℝ => circleTranslationEnergy (reflect u) z*z^(-1-2*ρ)) (Ioi 0) := by
    simpa only [translation_reflect] using hG
  have hh := add_le_add (hbound (reflect u) hGr) (hbound u hG)
  rw [square_reflect,gagliardo_reflect,← endpoint_integral_split ρ hρhalf u] at hh
  exact hh.trans_eq (by ring)

def boundaryDensity (ρ : ℝ) (c : AddCircle (1:ℝ)) (u : C(AddCircle (1:ℝ),ℂ)) (x : AddCircle (1:ℝ)) : ℝ :=
  (dist x c)^(-2*ρ)*‖u x‖^2

theorem boundary_shift (ρ : ℝ) (c : AddCircle (1:ℝ)) (u : C(AddCircle (1:ℝ),ℂ)) (x : AddCircle (1:ℝ)) :
    boundaryDensity ρ c u (x+c) = endpointDensity ρ (shift u c) x := by
  simp only [boundaryDensity,dist_eq_norm,add_sub_cancel_right,endpointDensity,shift,ContinuousMap.coe_mk]

theorem boundary_integrable {ρ : ℝ} (hρhalf : ρ < 1/2) (c : AddCircle (1:ℝ))
    (u : C(AddCircle (1:ℝ),ℂ)) : Integrable (boundaryDensity ρ c u) haarAddCircle := by
  apply ((measurePreserving_add_right haarAddCircle c).integrable_comp_emb
    (MeasurableEquiv.addRight c).measurableEmbedding).mp
  change Integrable (fun x => boundaryDensity ρ c u (x+c)) haarAddCircle
  simpa only [boundary_shift] using endpoint_integrable hρhalf (shift u c)

theorem exists_boundary_bound {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : C(AddCircle (1:ℝ),ℂ)) (c : AddCircle (1:ℝ)),
      IntegrableOn (fun z : ℝ => circleTranslationEnergy u z*z^(-1-2*ρ)) (Ioi 0) →
      (∫ x, boundaryDensity ρ c u x ∂haarAddCircle) ≤ C*(circleSquare u+circleFractionalSq ρ u) := by
  obtain ⟨C,hC,hbound⟩ := exists_endpoint_bound hρ hρhalf
  refine ⟨C,hC,?_⟩
  intro u c hG
  have hGs : IntegrableOn (fun z : ℝ => circleTranslationEnergy (shift u c) z*z^(-1-2*ρ)) (Ioi 0) := by
    simpa only [translation_shift] using hG
  have hh := hbound (shift u c) hGs
  rw [square_shift,gagliardo_shift] at hh
  calc
    _ = ∫ x, endpointDensity ρ (shift u c) x ∂haarAddCircle := by
      rw [← integral_add_right_eq_self (μ := haarAddCircle) (boundaryDensity ρ c u) c]
      simp only [boundary_shift]
    _ ≤ _ := hh

end SHE.IntervalSobolev
