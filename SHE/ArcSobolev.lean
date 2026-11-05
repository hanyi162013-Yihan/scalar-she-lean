module

public import SHE.IntervalSobolev
public import SHE.ArcGeometry

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.ArcSobolev
open Set MeasureTheory AddCircle CircleHeat CircleFractional FractionalHardy IntervalSobolev ArcGeometry
open scoped ENNReal
local instance arcSobolev_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance arcSobolev_nullSingleton : NullSingletonClass (@haarAddCircle (1:ℝ) _) where
  measure_singleton x := by
    have hv : (volume : Measure (AddCircle (1:ℝ))) = haarAddCircle := by
      simpa only [ENNReal.ofReal_one,one_smul] using AddCircle.volume_eq_smul_haarAddCircle (T := (1:ℝ))
    rw [← hv,← Metric.closedBall_zero,AddCircle.volume_closedBall]
    norm_num

def boundaryTail (ρ : ℝ) (c : AddCircle (1:ℝ)) (u : C(AddCircle (1:ℝ),ℂ))
    (x : AddCircle (1:ℝ)) (z : ℝ) : ℝ :=
  (Ici (dist x c)).indicator (fun z : ℝ => z^(-1-2*ρ)*‖u x‖^2) z

theorem boundaryTail_nonneg {ρ : ℝ} (c : AddCircle (1:ℝ)) (u : C(AddCircle (1:ℝ),ℂ))
    (x : AddCircle (1:ℝ)) {z : ℝ} (hz : 0 ≤ z) : 0 ≤ boundaryTail ρ c u x z := by
  unfold boundaryTail
  rw [Set.indicator_apply]
  split_ifs
  · exact mul_nonneg (Real.rpow_nonneg hz _) (sq_nonneg _)
  · exact le_rfl

theorem boundaryTail_integrable {ρ : ℝ} (hρ : 0 < ρ) (c : AddCircle (1:ℝ))
    (u : C(AddCircle (1:ℝ),ℂ)) {x : AddCircle (1:ℝ)} (hx : x ≠ c) :
    IntegrableOn (boundaryTail ρ c u x) (Ioi 0) := by
  have hd : 0 < dist x c := dist_pos.mpr hx
  have hi : IntegrableOn (fun z : ℝ => z^(-1-2*ρ)*‖u x‖^2) (Ici (dist x c)) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr
      ((integrableOn_Ioi_rpow_of_lt (by linarith) hd).mul_const _)
  exact hi.integrable_indicator measurableSet_Ici |>.integrableOn

theorem boundaryTail_integral {ρ : ℝ} (hρ : 0 < ρ) (c : AddCircle (1:ℝ))
    (u : C(AddCircle (1:ℝ),ℂ)) {x : AddCircle (1:ℝ)} (hx : x ≠ c) :
    (∫ z : ℝ in Ioi 0, boundaryTail ρ c u x z) = (2*ρ)⁻¹*boundaryDensity ρ c u x := by
  have hd : 0 < dist x c := dist_pos.mpr hx
  unfold boundaryTail
  rw [integral_indicator measurableSet_Ici,Measure.restrict_restrict measurableSet_Ici]
  rw [show Ici (dist x c) ∩ Ioi (0:ℝ) = Ici (dist x c) by
    ext z; simp only [mem_inter_iff,mem_Ici,mem_Ioi]; exact ⟨fun h => h.1,fun h => ⟨h,hd.trans_le h⟩⟩]
  rw [integral_mul_const,integral_Ici_eq_integral_Ioi,
    integral_Ioi_rpow_of_lt (by linarith : -1-2*ρ < -1) hd]
  simp only [boundaryDensity,show -1-2*ρ+1 = -2*ρ by ring]
  field_simp

theorem boundaryTail_measurable (ρ : ℝ) (c : AddCircle (1:ℝ))
    (u : C(AddCircle (1:ℝ),ℂ)) :
    Measurable (fun p : AddCircle (1:ℝ) × ℝ => boundaryTail ρ c u p.1 p.2) := by
  have hs : MeasurableSet {p : AddCircle (1:ℝ) × ℝ | dist p.1 c ≤ p.2} := by
    exact measurableSet_le (by fun_prop) measurable_snd
  have hi := (show Measurable (fun p : AddCircle (1:ℝ) × ℝ => p.2^(-1-2*ρ)*‖u p.1‖^2) by fun_prop).indicator hs
  convert hi using 1
  funext p
  simp only [boundaryTail,Set.indicator_apply,mem_Ici,mem_ofPred_eq]

theorem boundaryTail_product_integrable {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (c : AddCircle (1:ℝ)) (u : C(AddCircle (1:ℝ),ℂ)) :
    Integrable (fun p : AddCircle (1:ℝ) × ℝ => boundaryTail ρ c u p.1 p.2)
      (haarAddCircle.prod (volume.restrict (Ioi 0))) := by
  apply (integrable_prod_iff (boundaryTail_measurable ρ c u).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [haarAddCircle.ae_ne c] with x hx
    exact boundaryTail_integrable hρ c u hx
  · apply ((boundary_integrable hρhalf c u).const_mul ((2*ρ)⁻¹)).congr
    filter_upwards [haarAddCircle.ae_ne c] with x hx
    rw [← boundaryTail_integral hρ c u hx]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    exact (Real.norm_of_nonneg (boundaryTail_nonneg c u x hz.le)).symm

theorem boundaryTail_product_integral {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (c : AddCircle (1:ℝ)) (u : C(AddCircle (1:ℝ),ℂ)) :
    (∫ z : ℝ in Ioi 0, ∫ x, boundaryTail ρ c u x z ∂haarAddCircle) =
      (2*ρ)⁻¹*(∫ x, boundaryDensity ρ c u x ∂haarAddCircle) := by
  rw [← integral_integral_swap (boundaryTail_product_integrable hρ hρhalf c u)]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [haarAddCircle.ae_ne c] with x hx
  exact boundaryTail_integral hρ c u hx

def cutoff (a b : ℝ) (u : C(AddCircle (1:ℝ),ℂ)) : AddCircle (1:ℝ) → ℂ :=
  (arcSet a b).indicator u

theorem cutoff_measurable (a b : ℝ) (u : C(AddCircle (1:ℝ),ℂ)) : Measurable (cutoff a b u) :=
  u.continuous.measurable.indicator (measurableSet_arcSet a b)

theorem cutoff_difference_bound (ρ a b : ℝ) (u : C(AddCircle (1:ℝ),ℂ))
    (x : AddCircle (1:ℝ)) {z : ℝ} (hz : 0 ≤ z) :
    ‖cutoff a b u (x+(z : AddCircle (1:ℝ)))-cutoff a b u x‖^2*z^(-1-2*ρ) ≤
      2*(‖u (x+(z : AddCircle (1:ℝ)))-u x‖^2*z^(-1-2*ρ))+
        2*(boundaryTail ρ (a : AddCircle (1:ℝ)) u x z+boundaryTail ρ (b : AddCircle (1:ℝ)) u x z) := by
  have hk := Real.rpow_nonneg hz (-1-2*ρ)
  have hta := boundaryTail_nonneg (ρ := ρ) (a : AddCircle (1:ℝ)) u x hz
  have htb := boundaryTail_nonneg (ρ := ρ) (b : AddCircle (1:ℝ)) u x hz
  have hc (hc : (x ∈ arcSet a b ∧ x+(z : AddCircle (1:ℝ)) ∉ arcSet a b) ∨
      (x ∉ arcSet a b ∧ x+(z : AddCircle (1:ℝ)) ∈ arcSet a b)) :
      z^(-1-2*ρ)*‖u x‖^2 ≤ boundaryTail ρ (a : AddCircle (1:ℝ)) u x z+
        boundaryTail ρ (b : AddCircle (1:ℝ)) u x z := by
    rcases arc_crossing a b x hz hc with ha | hb
    · rw [boundaryTail,Set.indicator_of_mem (show z ∈ Ici (dist x (a : AddCircle (1:ℝ))) from ha)]
      exact le_add_of_nonneg_right htb
    · conv_rhs => rhs; unfold boundaryTail
      rw [Set.indicator_of_mem (show z ∈ Ici (dist x (b : AddCircle (1:ℝ))) from hb)]
      exact le_add_of_nonneg_left hta
  by_cases hx : x ∈ arcSet a b <;> by_cases hy : x+(z : AddCircle (1:ℝ)) ∈ arcSet a b
  · simp only [cutoff,Set.indicator_of_mem hx,Set.indicator_of_mem hy]
    nlinarith [mul_nonneg (sq_nonneg ‖u (x+(z : AddCircle (1:ℝ)))-u x‖) hk]
  · have hh := hc (Or.inl ⟨hx,hy⟩)
    simp only [cutoff,Set.indicator_of_mem hx,Set.indicator_of_notMem hy,zero_sub,norm_neg]
    nlinarith [mul_nonneg (sq_nonneg ‖u (x+(z : AddCircle (1:ℝ)))-u x‖) hk]
  · have hh := hc (Or.inr ⟨hx,hy⟩)
    have hn := norm_square_young 1 zero_lt_one (u (x+(z : AddCircle (1:ℝ)))) (u x)
    norm_num only [inv_one,one_add_one_eq_two] at hn
    have hm := mul_le_mul_of_nonneg_right hn hk
    simp only [cutoff,Set.indicator_of_notMem hx,Set.indicator_of_mem hy,sub_zero]
    nlinarith
  · simp only [cutoff,Set.indicator_of_notMem hx,Set.indicator_of_notMem hy,sub_self,norm_zero]
    norm_num only [zero_pow,mul_zero,zero_mul]
    nlinarith [mul_nonneg (sq_nonneg ‖u (x+(z : AddCircle (1:ℝ)))-u x‖) hk]

theorem positive_prod : ∀ᵐ p : ℝ × AddCircle (1:ℝ)
    ∂(volume.restrict (Ioi (0:ℝ))).prod haarAddCircle, 0 < p.1 := by
  apply (Measure.ae_prod_iff_ae_ae (by exact measurableSet_lt measurable_const measurable_fst)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  exact Filter.Eventually.of_forall (fun _ => hz)

theorem translation_product_integrable (ρ : ℝ) (u : C(AddCircle (1:ℝ),ℂ))
    (hG : IntegrableOn (fun z : ℝ => circleTranslationEnergy u z*z^(-1-2*ρ)) (Ioi 0)) :
    Integrable (fun p : ℝ × AddCircle (1:ℝ) => ‖u (p.2+(p.1 : AddCircle (1:ℝ)))-u p.2‖^2*p.1^(-1-2*ρ))
      ((volume.restrict (Ioi 0)).prod haarAddCircle) := by
  have hm : Measurable (fun p : ℝ × AddCircle (1:ℝ) => ‖u (p.2+(p.1 : AddCircle (1:ℝ)))-u p.2‖^2*p.1^(-1-2*ρ)) := by
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards with z
    have hi := (show Continuous (fun x : AddCircle (1:ℝ) => ‖u (x+(z : AddCircle (1:ℝ)))-u x‖^2) by fun_prop).continuousOn.integrableOn_compact (μ := haarAddCircle) isCompact_univ
    have hi' : Integrable (fun x : AddCircle (1:ℝ) => ‖u (x+(z : AddCircle (1:ℝ)))-u x‖^2) haarAddCircle := by
      simpa only [IntegrableOn,Measure.restrict_univ] using hi
    exact hi'.mul_const _
  · apply hG.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    simp only [circleTranslationEnergy,← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with x
    exact (Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hz.le _))).symm

theorem cutoff_product_integrable {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (a b : ℝ) (u : C(AddCircle (1:ℝ),ℂ))
    (hG : IntegrableOn (fun z : ℝ => circleTranslationEnergy u z*z^(-1-2*ρ)) (Ioi 0)) :
    Integrable (fun p : ℝ × AddCircle (1:ℝ) => ‖cutoff a b u (p.2+(p.1 : AddCircle (1:ℝ)))-cutoff a b u p.2‖^2*p.1^(-1-2*ρ))
      ((volume.restrict (Ioi 0)).prod haarAddCircle) := by
  have hmajor := ((translation_product_integrable ρ u hG).const_mul 2).add
    ((((boundaryTail_product_integrable hρ hρhalf (a : AddCircle (1:ℝ)) u).swap).add
      (boundaryTail_product_integrable hρ hρhalf (b : AddCircle (1:ℝ)) u).swap).const_mul 2)
  have hm : Measurable (fun p : ℝ × AddCircle (1:ℝ) => ‖cutoff a b u (p.2+(p.1 : AddCircle (1:ℝ)))-cutoff a b u p.2‖^2*p.1^(-1-2*ρ)) := by
    apply Measurable.mul
    · exact (((cutoff_measurable a b u).comp (by fun_prop)).sub ((cutoff_measurable a b u).comp measurable_snd)).norm.pow_const 2
    · fun_prop
  apply hmajor.mono' hm.aestronglyMeasurable
  filter_upwards [positive_prod] with p hp
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hp.le _))]
  exact cutoff_difference_bound ρ a b u p.2 hp.le

theorem cutoff_gagliardo_integrable {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (a b : ℝ) (u : C(AddCircle (1:ℝ),ℂ))
    (hG : IntegrableOn (fun z : ℝ => circleTranslationEnergy u z*z^(-1-2*ρ)) (Ioi 0)) :
    IntegrableOn (fun z : ℝ => circleTranslationEnergy (cutoff a b u) z*z^(-1-2*ρ)) (Ioi 0) := by
  have hi := (cutoff_product_integrable hρ hρhalf a b u hG).integral_prod_left
  simpa only [circleTranslationEnergy,integral_mul_const] using! hi

theorem cutoff_gagliardo_boundary_bound {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (a b : ℝ) (u : C(AddCircle (1:ℝ),ℂ))
    (hG : IntegrableOn (fun z : ℝ => circleTranslationEnergy u z*z^(-1-2*ρ)) (Ioi 0)) :
    circleFractionalSq ρ (cutoff a b u) ≤ 2*circleFractionalSq ρ u+
      2*((2*ρ)⁻¹*(∫ x, boundaryDensity ρ (a : AddCircle (1:ℝ)) u x ∂haarAddCircle)+
        (2*ρ)⁻¹*(∫ x, boundaryDensity ρ (b : AddCircle (1:ℝ)) u x ∂haarAddCircle)) := by
  have hc := cutoff_product_integrable hρ hρhalf a b u hG
  have hu := translation_product_integrable ρ u hG
  have ha := (boundaryTail_product_integrable hρ hρhalf (a : AddCircle (1:ℝ)) u).swap
  have hb := (boundaryTail_product_integrable hρ hρhalf (b : AddCircle (1:ℝ)) u).swap
  have hi := integral_mono_ae hc ((hu.const_mul 2).add ((ha.add hb).const_mul 2)) (by
    filter_upwards [positive_prod] with p hp
    exact cutoff_difference_bound ρ a b u p.2 hp.le)
  have hsplit := integral_add (hu.const_mul 2) ((ha.add hb).const_mul 2)
  dsimp only [Pi.add_apply] at hi hsplit
  rw [hsplit,integral_const_mul,integral_const_mul,integral_add ha hb] at hi
  rw [integral_prod _ hc,integral_prod _ hu,integral_prod _ ha,integral_prod _ hb] at hi
  simp only [Function.comp_apply,Prod.fst_swap,Prod.snd_swap,integral_mul_const,
    boundaryTail_product_integral hρ hρhalf] at hi
  simpa only [circleFractionalSq,circleTranslationEnergy] using! hi

theorem exists_cutoff_gagliardo_bound {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b : ℝ) (u : C(AddCircle (1:ℝ),ℂ)),
      IntegrableOn (fun z : ℝ => circleTranslationEnergy u z*z^(-1-2*ρ)) (Ioi 0) →
      circleFractionalSq ρ (cutoff a b u) ≤ C*(circleSquare u+circleFractionalSq ρ u) := by
  obtain ⟨C,hC,hbound⟩ := exists_boundary_bound hρ hρhalf
  refine ⟨2+4*(2*ρ)⁻¹*C,by positivity,?_⟩
  intro a b u hG
  have hh := cutoff_gagliardo_boundary_bound hρ hρhalf a b u hG
  have ha := hbound u (a : AddCircle (1:ℝ)) hG
  have hb := hbound u (b : AddCircle (1:ℝ)) hG
  have hn := circleSquare_nonneg u
  have hm : 0 ≤ (2*ρ)⁻¹ := by positivity
  nlinarith

end SHE.ArcSobolev
