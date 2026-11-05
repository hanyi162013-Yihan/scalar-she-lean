module

public import SHE.FractionalEnergy
public import SHE.HaarWeightedTaylor

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.FractionalHardy
open Finset Set MeasureTheory AddCircle CircleHeat CircleFractional
open scoped ENNReal
local instance fractionalHardy_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

def density (ρ : ℝ) (u : C(AddCircle (1:ℝ),ℂ)) (x : ℝ) : ℝ :=
  x^(-2*ρ)*‖u (x : AddCircle (1:ℝ))‖^2

def hardy (ρ r : ℝ) (u : C(AddCircle (1:ℝ),ℂ)) : ℝ := ∫ x in (0:ℝ)..r, density ρ u x

def difference (u : C(AddCircle (1:ℝ),ℂ)) (x z : ℝ) : ℝ :=
  ‖u ((x+z : ℝ) : AddCircle (1:ℝ)) - u (x : AddCircle (1:ℝ))‖^2

def dilationDifference (ρ r : ℝ) (u : C(AddCircle (1:ℝ),ℂ)) : ℝ :=
  ∫ a in (2:ℝ)..3, ∫ x in (0:ℝ)..r, x^(-2*ρ)*‖u ((a*x : ℝ) : AddCircle (1:ℝ))-u (x : AddCircle (1:ℝ))‖^2

theorem circle_integral_lift (g : AddCircle (1:ℝ) → ℝ) :
    (∫ x : ℝ in Ioc 0 1, g (x : AddCircle (1:ℝ))) = ∫ y, g y ∂haarAddCircle := by
  have hv : (volume : Measure (AddCircle (1:ℝ))) = haarAddCircle := by
    simpa only [ENNReal.ofReal_one,one_smul] using AddCircle.volume_eq_smul_haarAddCircle (T := (1:ℝ))
  rw [← hv]
  simpa only [zero_add] using AddCircle.integral_preimage (1:ℝ) 0 g

theorem weighted_bounded_integrable {ρ r M : ℝ} (hρhalf : ρ < 1/2) (_hr : 0 ≤ r) (_hM : 0 ≤ M)
    (F : ℝ → ℂ) (hF : Measurable F) (hbound : ∀ x, ‖F x‖ ≤ M) :
    IntegrableOn (fun x : ℝ => x^(-2*ρ)*‖F x‖^2) (Ioc 0 r) := by
  have hp : IntegrableOn (fun x : ℝ => x^(-2*ρ)) (Ioc 0 r) := by
    exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < -2*ρ) :
      IntervalIntegrable (fun x : ℝ => x^(-2*ρ)) volume 0 r).1.mono_set (by exact Subset.rfl)
  apply (hp.mul_const (M^2)).mono'
  · exact ((by fun_prop : Measurable (fun x : ℝ => x^(-2*ρ))).mul (hF.norm.pow_const 2)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hx.1.le _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hbound x) 2) (Real.rpow_nonneg hx.1.le _)

theorem density_integrable {ρ r : ℝ} (hρhalf : ρ < 1/2) (hr : 0 ≤ r)
    (u : C(AddCircle (1:ℝ),ℂ)) : IntegrableOn (density ρ u) (Ioc 0 r) := by
  apply weighted_bounded_integrable hρhalf hr (norm_nonneg u)
  · exact u.continuous.measurable.comp AddCircle.measurable_mk'
  · exact fun x => u.norm_coe_le_norm _

theorem density_intervalIntegrable {ρ r : ℝ} (hρhalf : ρ < 1/2) (hr : 0 ≤ r)
    (u : C(AddCircle (1:ℝ),ℂ)) : IntervalIntegrable (density ρ u) volume 0 r :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hr).mpr (density_integrable hρhalf hr u)

theorem density_nonneg (ρ : ℝ) (u : C(AddCircle (1:ℝ),ℂ)) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ density ρ u x := mul_nonneg (Real.rpow_nonneg hx _) (sq_nonneg _)

theorem hardy_nonneg {ρ r : ℝ} (hr : 0 ≤ r) (u : C(AddCircle (1:ℝ),ℂ)) : 0 ≤ hardy ρ r u := by
  apply intervalIntegral.integral_nonneg hr
  intro x hx
  exact density_nonneg ρ u hx.1

theorem dilation_integrable {ρ r a : ℝ} (hρhalf : ρ < 1/2) (hr : 0 ≤ r)
    (u : C(AddCircle (1:ℝ),ℂ)) :
    IntervalIntegrable (fun x : ℝ => x^(-2*ρ)*‖u ((a*x : ℝ) : AddCircle (1:ℝ))‖^2) volume 0 r := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hr).mpr
  apply weighted_bounded_integrable hρhalf hr (norm_nonneg u)
  · fun_prop
  · exact fun x => u.norm_coe_le_norm _

theorem dilation_difference_integrable {ρ r a : ℝ} (hρhalf : ρ < 1/2) (hr : 0 ≤ r)
    (u : C(AddCircle (1:ℝ),ℂ)) :
    IntervalIntegrable (fun x : ℝ => x^(-2*ρ)*
      ‖u ((a*x : ℝ) : AddCircle (1:ℝ))-u (x : AddCircle (1:ℝ))‖^2) volume 0 r := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hr).mpr
  apply weighted_bounded_integrable hρhalf hr (by positivity : 0 ≤ 2*‖u‖)
  · fun_prop
  · intro x
    exact (norm_sub_le _ _).trans ((add_le_add (u.norm_coe_le_norm _) (u.norm_coe_le_norm _)).trans_eq (by ring))

theorem dilation_density_rescale {ρ r a : ℝ} (_hρhalf : ρ < 1/2) (hr : 0 ≤ r) (ha : 0 < a)
    (u : C(AddCircle (1:ℝ),ℂ)) :
    (∫ x in (0:ℝ)..r, x^(-2*ρ)*‖u ((a*x : ℝ) : AddCircle (1:ℝ))‖^2) =
      a^(2*ρ-1)*hardy ρ (a*r) u := by
  calc
    _ = ∫ x in (0:ℝ)..r, a^(2*ρ)*density ρ u (a*x) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with x
      intro hx
      have hx' : 0 < x := by rw [uIoc_of_le hr] at hx; exact hx.1
      unfold density
      rw [Real.mul_rpow ha.le hx'.le]
      have he : a^(2*ρ)*a^(-2*ρ) = 1 := by rw [← Real.rpow_add ha]; simp
      rw [← mul_assoc,← mul_assoc,he,one_mul]
    _ = a^(2*ρ)*(a⁻¹*hardy ρ (a*r) u) := by
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_mul_left _ ha.ne']
      simp only [mul_zero,smul_eq_mul,hardy]
    _ = _ := by
      rw [← mul_assoc,← Real.rpow_neg_one a,← Real.rpow_add ha]
      congr 2

theorem norm_square_young (η : ℝ) (hη : 0 < η) (z w : ℂ) :
    ‖z‖^2 ≤ (1+η)*‖w‖^2+(1+η⁻¹)*‖z-w‖^2 := by
  have ht : ‖z‖ ≤ ‖w‖+‖z-w‖ := by
    calc
      _ = ‖w+(z-w)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  have hs := sq_nonneg (Real.sqrt η*‖w‖-(Real.sqrt η)⁻¹*‖z-w‖)
  have he := Real.sq_sqrt hη.le
  have hne : Real.sqrt η ≠ 0 := (Real.sqrt_pos.mpr hη).ne'
  have hrel : (Real.sqrt η)⁻¹^2 = η⁻¹ := by rw [inv_pow,he]
  have hcross : (Real.sqrt η*‖w‖)*((Real.sqrt η)⁻¹*‖z-w‖) = ‖w‖*‖z-w‖ := by field_simp
  nlinarith [sq_le_sq₀ (norm_nonneg z) (by positivity : 0 ≤ ‖w‖+‖z-w‖) |>.mpr ht]

theorem weighted_product_integrable {ρ r M : ℝ} (hρhalf : ρ < 1/2) (hr : 0 ≤ r) (_hM : 0 ≤ M)
    (F : ℝ × ℝ → ℂ) (hF : Measurable F) (hbound : ∀ p, ‖F p‖ ≤ M) :
    Integrable (fun p : ℝ × ℝ => p.2^(-2*ρ)*‖F p‖^2)
      ((volume.restrict (Ioc (2:ℝ) 3)).prod (volume.restrict (Ioc 0 r))) := by
  have hp : IntegrableOn (fun x : ℝ => x^(-2*ρ)) (Ioc 0 r) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hr).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < -2*ρ))
  apply ((hp.mul_const (M^2)).comp_snd (volume.restrict (Ioc (2:ℝ) 3))).mono'
  · exact ((by fun_prop : Measurable (fun p : ℝ × ℝ => p.2^(-2*ρ))).mul
      (hF.norm.pow_const 2)).aestronglyMeasurable
  · filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)] with p hp
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hp.1.le _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hbound p) 2)
      (Real.rpow_nonneg hp.1.le _)

theorem dilation_difference_outer_integrable {ρ r : ℝ} (hρhalf : ρ < 1/2) (hr : 0 ≤ r)
    (u : C(AddCircle (1:ℝ),ℂ)) : IntervalIntegrable (fun a : ℝ => ∫ x in (0:ℝ)..r,
      x^(-2*ρ)*‖u ((a*x : ℝ) : AddCircle (1:ℝ))-u (x : AddCircle (1:ℝ))‖^2) volume 2 3 := by
  have hprod := weighted_product_integrable hρhalf hr (by positivity : 0 ≤ 2*‖u‖)
    (fun p : ℝ × ℝ => u ((p.1*p.2 : ℝ) : AddCircle (1:ℝ))-u (p.2 : AddCircle (1:ℝ)))
    (by fun_prop) (fun p => (norm_sub_le _ _).trans
      ((add_le_add (u.norm_coe_le_norm _) (u.norm_coe_le_norm _)).trans_eq (by ring)))
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (2:ℝ) ≤ 3)).mpr
  change Integrable _ (volume.restrict (Ioc (2:ℝ) 3))
  simpa only [intervalIntegral.integral_of_le hr] using hprod.integral_prod_left

theorem dilationDifference_nonneg {ρ r : ℝ} (hr : 0 ≤ r) (u : C(AddCircle (1:ℝ),ℂ)) :
    0 ≤ dilationDifference ρ r u := by
  apply intervalIntegral.integral_nonneg (by norm_num : (2:ℝ) ≤ 3)
  intro a ha
  apply intervalIntegral.integral_nonneg hr
  intro x hx
  exact mul_nonneg (Real.rpow_nonneg hx.1 _) (sq_nonneg _)

theorem hardy_mono {ρ r s : ℝ} (hρhalf : ρ < 1/2) (hr : 0 ≤ r) (hrs : r ≤ s)
    (u : C(AddCircle (1:ℝ),ℂ)) : hardy ρ r u ≤ hardy ρ s u := by
  rw [hardy,hardy,intervalIntegral.integral_of_le hr,intervalIntegral.integral_of_le (hr.trans hrs)]
  apply setIntegral_mono_set (density_integrable hρhalf (hr.trans hrs) u)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact density_nonneg ρ u hx.1.le
  · exact ae_of_all _ (fun x hx => (Ioc_subset_Ioc le_rfl hrs) hx)

theorem hardy_averaged_dilation {ρ η : ℝ} (hρhalf : ρ < 1/2) (hη : 0 < η)
    (u : C(AddCircle (1:ℝ),ℂ)) :
    hardy ρ (1/4) u ≤ (1+η)*(2:ℝ)^(2*ρ-1)*hardy ρ (3/4) u +
      (1+η⁻¹)*dilationDifference ρ (1/4) u := by
  have hr : (0:ℝ) ≤ 1/4 := by norm_num
  have hD := dilation_difference_outer_integrable hρhalf hr u
  have hpoint (a : ℝ) (ha : a ∈ Ioc (2:ℝ) 3) :
      hardy ρ (1/4) u ≤ (1+η)*(2:ℝ)^(2*ρ-1)*hardy ρ (3/4) u + (1+η⁻¹)*
        (∫ x in (0:ℝ)..(1/4:ℝ), x^(-2*ρ)*‖u ((a*x : ℝ) : AddCircle (1:ℝ))-u (x : AddCircle (1:ℝ))‖^2) := by
    have ha0 : 0 < a := lt_trans (by norm_num : (0:ℝ)<2) ha.1
    have hmono : a^(2*ρ-1) ≤ (2:ℝ)^(2*ρ-1) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) ha.1.le (by linarith)
    have hscale : hardy ρ (a*(1/4)) u ≤ hardy ρ (3/4) u :=
      hardy_mono hρhalf (by positivity) (by nlinarith [ha.2]) u
    have hi : hardy ρ (1/4) u ≤ (1+η)*
        (∫ x in (0:ℝ)..(1/4:ℝ), x^(-2*ρ)*‖u ((a*x : ℝ) : AddCircle (1:ℝ))‖^2) + (1+η⁻¹)*
        (∫ x in (0:ℝ)..(1/4:ℝ), x^(-2*ρ)*‖u ((a*x : ℝ) : AddCircle (1:ℝ))-u (x : AddCircle (1:ℝ))‖^2) := by
      rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add ((dilation_integrable hρhalf hr u).const_mul (1+η))
          ((dilation_difference_integrable hρhalf hr u).const_mul (1+η⁻¹))]
      apply intervalIntegral.integral_mono_on hr (density_intervalIntegrable hρhalf hr u)
        (((dilation_integrable hρhalf hr u).const_mul (1+η)).add
          ((dilation_difference_integrable hρhalf hr u).const_mul (1+η⁻¹)))
      intro x hx
      have hy := norm_square_young η hη (u (x : AddCircle (1:ℝ))) (u ((a*x : ℝ) : AddCircle (1:ℝ)))
      rw [norm_sub_rev] at hy
      have hh := mul_le_mul_of_nonneg_left hy (Real.rpow_nonneg hx.1 (-2*ρ))
      dsimp only [density]
      nlinarith only [hh]
    rw [dilation_density_rescale hρhalf hr ha0] at hi
    exact hi.trans (add_le_add
      ((mul_le_mul_of_nonneg_left (mul_le_mul hmono hscale (hardy_nonneg (by positivity) u)
        (Real.rpow_nonneg (by norm_num) _)) (by positivity)).trans_eq (by ring)) le_rfl)
  have hset : (∫ a : ℝ in Ioc 2 3, hardy ρ (1/4) u) ≤
      ∫ a : ℝ in Ioc 2 3, ((1+η)*(2:ℝ)^(2*ρ-1)*hardy ρ (3/4) u + (1+η⁻¹)*
        (∫ x in (0:ℝ)..(1/4:ℝ), x^(-2*ρ)*‖u ((a*x : ℝ) : AddCircle (1:ℝ))-u (x : AddCircle (1:ℝ))‖^2)) := by
    apply integral_mono_ae (integrable_const _)
      ((integrable_const _).add (hD.1.const_mul (1+η⁻¹)))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
    exact hpoint a ha
  have hs := hset
  rw [integral_add (integrable_const _) (hD.1.const_mul (1+η⁻¹))] at hs
  simp only [integral_const_mul,integral_const,smul_eq_mul] at hs
  norm_num at hs
  simpa only [dilationDifference,intervalIntegral.integral_of_le (by norm_num : (2:ℝ) ≤ 3),neg_mul] using hs

theorem difference_integrable (u : C(AddCircle (1:ℝ),ℂ)) (z : ℝ) :
    IntegrableOn (fun x : ℝ => difference u x z) (Ioc 0 1) := by
  have hc : Continuous (fun x : ℝ => difference u x z) := by unfold difference; fun_prop
  exact (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self

theorem difference_lift_integral (u : C(AddCircle (1:ℝ),ℂ)) (z : ℝ) :
    (∫ x : ℝ in Ioc 0 1, difference u x z) = circleTranslationEnergy u z := by
  unfold difference circleTranslationEnergy
  simpa only [QuotientAddGroup.mk_add] using circle_integral_lift
    (fun x : AddCircle (1:ℝ) => ‖u (x+(z : AddCircle (1:ℝ)))-u x‖^2)

theorem gagliardo_product_integrable {ρ : ℝ} (u : C(AddCircle (1:ℝ),ℂ))
    (hG : IntegrableOn (fun z : ℝ => circleTranslationEnergy u z*z^(-1-2*ρ)) (Ioi 0)) :
    Integrable (fun p : ℝ × ℝ => difference u p.2 p.1*p.1^(-1-2*ρ))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioc (0:ℝ) 1))) := by
  have hm : Measurable (fun p : ℝ × ℝ => difference u p.2 p.1*p.1^(-1-2*ρ)) := by
    unfold difference
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards with z
    change Integrable (fun x : ℝ => difference u x z*z^(-1-2*ρ)) (volume.restrict (Ioc (0:ℝ) 1))
    exact (difference_integrable u z).mul_const _
  · change Integrable _ (volume.restrict (Ioi (0:ℝ)))
    apply hG.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    symm
    calc
      _ = ∫ x : ℝ in Ioc 0 1, difference u x z*z^(-1-2*ρ) := by
        apply integral_congr_ae
        filter_upwards with x
        exact Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hz.le _))
      _ = _ := by rw [integral_mul_const,difference_lift_integral]

theorem gagliardo_local_bound {ρ r : ℝ} (_hr : 0 ≤ r) (hr1 : r ≤ 1)
    (u : C(AddCircle (1:ℝ),ℂ))
    (hG : IntegrableOn (fun z : ℝ => circleTranslationEnergy u z*z^(-1-2*ρ)) (Ioi 0)) :
    (∫ x : ℝ in Ioc 0 r, ∫ z : ℝ in Ioi 0, difference u x z*z^(-1-2*ρ)) ≤ circleFractionalSq ρ u := by
  have hprod := gagliardo_product_integrable u hG
  calc
    _ ≤ ∫ x : ℝ in Ioc 0 1, ∫ z : ℝ in Ioi 0, difference u x z*z^(-1-2*ρ) := by
      apply setIntegral_mono_set hprod.integral_prod_right
      · filter_upwards with x
        apply integral_nonneg_of_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
        exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hz.le _)
      · exact ae_of_all _ (fun x hx => (Ioc_subset_Ioc le_rfl hr1) hx)
    _ = ∫ z : ℝ in Ioi 0, ∫ x : ℝ in Ioc 0 1, difference u x z*z^(-1-2*ρ) :=
      (integral_integral_swap hprod).symm
    _ = _ := by
      unfold circleFractionalSq
      apply integral_congr_ae
      filter_upwards with z
      rw [integral_mul_const,difference_lift_integral]

theorem dilation_difference_change {ρ x : ℝ} (hx : 0 < x)
    (u : C(AddCircle (1:ℝ),ℂ)) :
    (∫ a in (2:ℝ)..3, x^(-2*ρ)*‖u ((a*x : ℝ) : AddCircle (1:ℝ))-u (x : AddCircle (1:ℝ))‖^2) =
      x^(-1-2*ρ)*(∫ z in x..2*x, difference u x z) := by
  rw [intervalIntegral.integral_const_mul]
  have he : (fun a : ℝ => ‖u ((a*x : ℝ) : AddCircle (1:ℝ))-u (x : AddCircle (1:ℝ))‖^2) =
      fun a => difference u x (x*a+(-x)) := by
    funext a
    unfold difference
    rw [show x+(x*a+(-x)) = a*x by ring]
  rw [he,intervalIntegral.integral_comp_mul_add _ hx.ne' (-x)]
  rw [show x*2+(-x) = x by ring,show x*3+(-x) = 2*x by ring]
  simp only [smul_eq_mul]
  rw [← mul_assoc,← Real.rpow_neg_one x,← Real.rpow_add hx]
  rw [show -2*ρ+(-1:ℝ) = -1-2*ρ by ring]

theorem local_weight_comparison {ρ x z : ℝ} (hρ : 0 < ρ) (hx : 0 < x)
    (hz : z ∈ Ioc x (2*x)) :
    x^(-1-2*ρ) ≤ (2:ℝ)^(1+2*ρ)*z^(-1-2*ρ) := by
  have hz0 : 0 < z := hx.trans hz.1
  have hh : x^(-1-2*ρ) ≤ (z/2)^(-1-2*ρ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [hz.2]) (by linarith)
  apply hh.trans_eq
  rw [Real.div_rpow hz0.le (by norm_num),div_eq_mul_inv,← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  rw [show -(-1-2*ρ) = 1+2*ρ by ring]
  ring

theorem dilation_difference_pointwise_bound {ρ x : ℝ} (hρ : 0 < ρ) (hx : 0 < x)
    (u : C(AddCircle (1:ℝ),ℂ))
    (hi : IntegrableOn (fun z : ℝ => difference u x z*z^(-1-2*ρ)) (Ioi 0)) :
    (∫ a in (2:ℝ)..3, x^(-2*ρ)*‖u ((a*x : ℝ) : AddCircle (1:ℝ))-u (x : AddCircle (1:ℝ))‖^2) ≤
      (2:ℝ)^(1+2*ρ)*(∫ z : ℝ in Ioi 0, difference u x z*z^(-1-2*ρ)) := by
  have hsub : Ioc x (2*x) ⊆ Ioi (0:ℝ) := fun z hz => hx.trans hz.1
  have hc : Continuous (fun z : ℝ => difference u x z) := by unfold difference; fun_prop
  have hd : IntegrableOn (fun z : ℝ => difference u x z) (Ioc x (2*x)) :=
    (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  rw [dilation_difference_change hx u,intervalIntegral.integral_of_le (by linarith : x ≤ 2*x)]
  calc
    _ = ∫ z : ℝ in Ioc x (2*x), x^(-1-2*ρ)*difference u x z := (integral_const_mul _ _).symm
    _ ≤ ∫ z : ℝ in Ioc x (2*x), (2:ℝ)^(1+2*ρ)*(difference u x z*z^(-1-2*ρ)) := by
      apply integral_mono_ae (hd.const_mul _) ((hi.mono_set hsub).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
      exact (mul_le_mul_of_nonneg_right (local_weight_comparison hρ hx hz) (sq_nonneg _)).trans_eq (by unfold difference; ring)
    _ = (2:ℝ)^(1+2*ρ)*(∫ z : ℝ in Ioc x (2*x), difference u x z*z^(-1-2*ρ)) := integral_const_mul _ _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply setIntegral_mono_set hi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
        exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hz.le _)
      · exact ae_of_all _ (fun z hz => hsub hz)

/-- The actual dilation error is controlled by the true periodic
Gagliardo form. Both changes of variable and summation orders are
performed on the physical spatial integrals. -/
theorem dilationDifference_le_gagliardo {ρ r : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (u : C(AddCircle (1:ℝ),ℂ))
    (hG : IntegrableOn (fun z : ℝ => circleTranslationEnergy u z*z^(-1-2*ρ)) (Ioi 0)) :
    dilationDifference ρ r u ≤ (2:ℝ)^(1+2*ρ)*circleFractionalSq ρ u := by
  have hprodD := weighted_product_integrable hρhalf hr (by positivity : 0 ≤ 2*‖u‖)
    (fun p : ℝ × ℝ => u ((p.1*p.2 : ℝ) : AddCircle (1:ℝ))-u (p.2 : AddCircle (1:ℝ)))
    (by fun_prop) (fun p => (norm_sub_le _ _).trans
      ((add_le_add (u.norm_coe_le_norm _) (u.norm_coe_le_norm _)).trans_eq (by ring)))
  have hprodG := gagliardo_product_integrable u hG
  have hiG : Integrable (fun x : ℝ => ∫ z : ℝ in Ioi 0, difference u x z*z^(-1-2*ρ))
      (volume.restrict (Ioc 0 r)) := hprodG.integral_prod_right.mono_measure
        (Measure.restrict_mono_set volume (Ioc_subset_Ioc le_rfl hr1))
  have hrows : ∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) r),
      IntegrableOn (fun z : ℝ => difference u x z*z^(-1-2*ρ)) (Ioi 0) := by
    exact (hprodG.prod_left_ae).filter_mono
      (ae_mono (Measure.restrict_mono_set volume (Ioc_subset_Ioc le_rfl hr1)))
  unfold dilationDifference
  rw [intervalIntegral.integral_of_le (by norm_num : (2:ℝ) ≤ 3)]
  simp only [intervalIntegral.integral_of_le hr]
  rw [integral_integral_swap hprodD]
  calc
    _ ≤ ∫ x : ℝ in Ioc 0 r, (2:ℝ)^(1+2*ρ)*(∫ z : ℝ in Ioi 0, difference u x z*z^(-1-2*ρ)) := by
      apply integral_mono_ae hprodD.integral_prod_right (hiG.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc,hrows] with x hx hi
      have hh := dilation_difference_pointwise_bound hρ hx.1 u hi
      simpa only [intervalIntegral.integral_of_le (by norm_num : (2:ℝ) ≤ 3)] using hh
    _ = (2:ℝ)^(1+2*ρ)*(∫ x : ℝ in Ioc 0 r, ∫ z : ℝ in Ioi 0, difference u x z*z^(-1-2*ρ)) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (gagliardo_local_bound hr hr1 u hG) (by positivity)

def circleSquare (u : C(AddCircle (1:ℝ),ℂ)) : ℝ := ∫ x, ‖u x‖^2 ∂haarAddCircle

theorem circleSquare_nonneg (u : C(AddCircle (1:ℝ),ℂ)) : 0 ≤ circleSquare u :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem gagliardo_nonneg (ρ : ℝ) (u : C(AddCircle (1:ℝ),ℂ)) : 0 ≤ circleFractionalSq ρ u := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  exact mul_nonneg (integral_nonneg (fun _ => sq_nonneg _)) (Real.rpow_nonneg hz.le _)

theorem hardy_tail_bound {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (u : C(AddCircle (1:ℝ),ℂ)) :
    hardy ρ (3/4) u ≤ hardy ρ (1/4) u + (1/4:ℝ)^(-2*ρ)*circleSquare u := by
  have htail : IntervalIntegrable (density ρ u) volume (1/4) (3/4) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1/4:ℝ) ≤ 3/4)).mpr
      ((density_integrable hρhalf (by norm_num : (0:ℝ) ≤ 3/4) u).mono_set
        (Ioc_subset_Ioc (by norm_num : (0:ℝ) ≤ 1/4) le_rfl))
  have hdecomp : hardy ρ (3/4) u = hardy ρ (1/4) u + ∫ x in (1/4:ℝ)..(3/4:ℝ), density ρ u x := by
    unfold hardy
    exact (intervalIntegral.integral_add_adjacent_intervals
      (density_intervalIntegrable hρhalf (by norm_num : (0:ℝ) ≤ 1/4) u) htail).symm
  have hnorm : IntegrableOn (fun x : ℝ => ‖u (x : AddCircle (1:ℝ))‖^2) (Ioc 0 1) := by
    exact ((by fun_prop : Continuous (fun x : ℝ => ‖u (x : AddCircle (1:ℝ))‖^2)).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  rw [hdecomp]
  apply add_le_add le_rfl
  rw [intervalIntegral.integral_of_le (by norm_num : (1/4:ℝ) ≤ 3/4)]
  calc
    _ ≤ ∫ x : ℝ in Ioc (1/4:ℝ) (3/4:ℝ), (1/4:ℝ)^(-2*ρ)*‖u (x : AddCircle (1:ℝ))‖^2 := by
      apply integral_mono_ae htail.1
        ((hnorm.mono_set (Ioc_subset_Ioc (by norm_num) (by norm_num))).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ)<1/4) hx.1.le (by linarith)) (sq_nonneg _)
    _ ≤ ∫ x : ℝ in Ioc 0 1, (1/4:ℝ)^(-2*ρ)*‖u (x : AddCircle (1:ℝ))‖^2 := by
      apply setIntegral_mono_set (hnorm.const_mul _)
      · exact ae_of_all _ (fun _ => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (sq_nonneg _))
      · exact ae_of_all _ (fun x hx => ⟨lt_trans (by norm_num : (0:ℝ)<1/4) hx.1,
          le_trans hx.2 (by norm_num : (3/4:ℝ) ≤ 1)⟩)
    _ = _ := by
      rw [integral_const_mul]
      exact congrArg (fun v : ℝ => (1/4:ℝ)^(-2*ρ)*v)
        (circle_integral_lift (fun y : AddCircle (1:ℝ) => ‖u y‖^2))

/-- The genuine endpoint fractional Hardy inequality on the periodic
circle, for `0<ρ<1/2`. Its constant is uniform over all continuous inputs.
The absorption coefficient is the actual dilation factor `2^(2ρ−1)<1`.
No boundary-weight estimate is assumed. -/
theorem exists_hardy_bound {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : C(AddCircle (1:ℝ),ℂ),
      IntegrableOn (fun z : ℝ => circleTranslationEnergy u z*z^(-1-2*ρ)) (Ioi 0) →
      hardy ρ (1/4) u ≤ C*(circleSquare u+circleFractionalSq ρ u) := by
  let θ : ℝ := (2:ℝ)^(2*ρ-1)
  have hθ : 0 < θ := Real.rpow_pos_of_pos (by norm_num) _
  have hθ1 : θ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  let η : ℝ := (1-θ)/(2*θ)
  have hη : 0 < η := div_pos (sub_pos.mpr hθ1) (mul_pos (by norm_num) hθ)
  let k : ℝ := (1+η)*θ
  let l : ℝ := 1+η⁻¹
  let c : ℝ := (1/4:ℝ)^(-2*ρ)
  let K : ℝ := (2:ℝ)^(1+2*ρ)
  have hk : 0 < k := mul_pos (by dsimp [η]; positivity) hθ
  have hk1 : k < 1 := by
    have he : k = (1+θ)/2 := by dsimp only [k,η]; field_simp; ring
    rw [he]
    linarith
  have hl : 0 < l := by dsimp only [l]; positivity
  have hc : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  have hK : 0 < K := Real.rpow_pos_of_pos (by norm_num) _
  let C : ℝ := (k*c+l*K)/(1-k)
  have hC : 0 < C := div_pos (add_pos (mul_pos hk hc) (mul_pos hl hK)) (sub_pos.mpr hk1)
  refine ⟨C,hC,?_⟩
  intro u hG
  have ha := hardy_averaged_dilation hρhalf hη u
  have ht := hardy_tail_bound hρ hρhalf u
  have hd := dilationDifference_le_gagliardo hρ hρhalf (by norm_num : (0:ℝ) ≤ 1/4)
    (by norm_num : (1/4:ℝ) ≤ 1) u hG
  change hardy ρ (1/4) u ≤ k*hardy ρ (3/4) u+l*dilationDifference ρ (1/4) u at ha
  change hardy ρ (3/4) u ≤ hardy ρ (1/4) u+c*circleSquare u at ht
  change dilationDifference ρ (1/4) u ≤ K*circleFractionalSq ρ u at hd
  have hh := ha.trans (add_le_add (mul_le_mul_of_nonneg_left ht hk.le) (mul_le_mul_of_nonneg_left hd hl.le))
  have hS := circleSquare_nonneg u
  have hG0 := gagliardo_nonneg ρ u
  dsimp only [C]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sub_pos.mpr hk1)).mpr
  have hcross := add_nonneg (mul_nonneg (mul_nonneg hk.le hc.le) hG0) (mul_nonneg (mul_nonneg hl.le hK.le) hS)
  nlinarith only [hh,hcross]

end SHE.FractionalHardy
