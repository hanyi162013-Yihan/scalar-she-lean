module

public import SHE.PhysicalProfile
public import SHE.CanonicalProfile

@[expose] public section
set_option autoImplicit false

/-! Pointwise parameter control of actual scalar profiles. The spatially uniform
bound here is a domination device; the sharper one-input spatial L² estimate
remains the separate theorem in `ProfileStability`. -/
noncomputable section
namespace SHE.ProfilePointwise
open Set MeasureTheory AddCircle StoppedFourier ProfileVariance GaussianProfile
open ProfileL2 ProfileStability PhysicalProfile

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- A genuine weighted estimate for the physical heat-square covariance map. -/
theorem varianceMap_weighted_bound {c : ℝ × HeatCircle → ℝ} {r M S a : ℝ}
    (hc : Measurable c) (hr : 0 < r) (hr1 : r ≤ 1) (hM : 0 ≤ M)
    (hS : 0 ≤ S) (ha : -1 < a)
    (hbound : ∀ s ∈ Ioo 0 r, ∀ y, |c (s, y)| ≤ M)
    (hweight : ∀ s ∈ Ioo 0 r, ∀ y, |c (s, y)| ≤ S * s ^ a) (x : HeatCircle) :
    |varianceMap c r x| ≤ (1 + heatConstant) * S *
      ProfileVolterra.powerConstant a * r ^ (a + 1 / 2) := by
  have hi := (varianceMap_bound hc hr hr1 hM hbound x).1
  have hp := ProfileVolterra.singular_convolution_bound ha hr hS
    (by fun_prop : Measurable (fun s : ℝ => S * s ^ a))
    (fun s hs => mul_nonneg hS (Real.rpow_nonneg hs.1.le _))
    (fun _ _ => le_rfl)
  have hK : 0 ≤ 1 + heatConstant := by linarith [heatConstant_pos]
  have hb : ∀ s ∈ Ioo 0 r, |varianceDensity c r x s| ≤
      (1 + heatConstant) * ((r - s) ^ (-(1 / 2 : ℝ)) * (S * s ^ a)) := by
    intro s hs
    have hv := varianceDensity_bound hc
      (mul_nonneg hS (Real.rpow_nonneg hs.1.le _)) hs.2 (hweight s hs) x
    have hm := mul_le_mul_of_nonneg_left (heat_mass_small_time
      (show 0 < r - s by linarith [hs.2]) (show r - s ≤ 1 by linarith [hs.1]) x)
      (mul_nonneg hS (Real.rpow_nonneg hs.1.le a))
    exact hv.trans (by nlinarith only [hm])
  rw [show varianceMap c r x = ∫ s in (0 : ℝ)..r, varianceDensity c r x s from rfl]
  calc
    _ ≤ ∫ s in (0 : ℝ)..r, |varianceDensity c r x s| := by
      simpa only [Real.norm_eq_abs] using
        intervalIntegral.norm_integral_le_integral_norm (f := varianceDensity c r x) hr.le
    _ ≤ ∫ s in (0 : ℝ)..r,
        (1 + heatConstant) * ((r - s) ^ (-(1 / 2 : ℝ)) * (S * s ^ a)) :=
      intervalIntegral.integral_mono_on_of_le_Ioo hr.le hi.norm (hp.1.const_mul _) hb
    _ = (1 + heatConstant) * (∫ s in (0 : ℝ)..r,
        (r - s) ^ (-(1 / 2 : ℝ)) * (S * s ^ a)) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ (1 + heatConstant) * (S * ProfileVolterra.powerConstant a * r ^ (a + 1 / 2)) :=
      mul_le_mul_of_nonneg_left hp.2 hK
    _ = _ := by ring

/-- The actual physical heat mean has the short-time L² to pointwise bound. -/
theorem physicalHeatMean_pointwise {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (d : CircleL2) (x : HeatCircle) :
    |physicalHeatMean d (r, x)| ≤ Real.sqrt (1 + heatConstant) *
      r ^ (-(1 / 4 : ℝ)) * ‖d‖ := by
  rw [physicalHeatMean_eq hr]
  have hnorm : ‖circleHeat r x‖ ≤ Real.sqrt (1 + heatConstant) * r ^ (-(1 / 4 : ℝ)) := by
    have hmass := heat_mass_small_time hr hr1 x
    have hp : (Real.sqrt (1 + heatConstant) * r ^ (-(1 / 4 : ℝ))) ^ 2 =
        (1 + heatConstant) * r ^ (-(1 / 2 : ℝ)) := by
      rw [mul_pow, Real.sq_sqrt (by linarith [heatConstant_pos] : 0 ≤ 1 + heatConstant),
        ← Real.rpow_mul_natCast hr.le]
      norm_num
    have hn : 0 ≤ Real.sqrt (1 + heatConstant) * r ^ (-(1 / 4 : ℝ)) := by positivity
    nlinarith [norm_nonneg (circleHeat r x)]
  exact (Complex.abs_re_le_norm _).trans
    ((norm_inner_le_norm (𝕜 := ℂ) (circleHeat r x) d).trans
      (mul_le_mul_of_nonneg_right hnorm (norm_nonneg d)))

/-- Weighted absorption over all spatial points, without a measurability
assumption on the spatial supremum. The covariance is the actual heat-square
integral, not an abstract supplied transfer operator. -/
theorem spatial_weighted_absorption {c d : ℝ × HeatCircle → ℝ}
    {a b θ h A B M : ℝ} (hc : Measurable c) (hd : Measurable d)
    (ha : -1 < a) (ha0 : a ≤ 0) (hθ : 0 < θ) (hbθ : b + 1 / 2 = θ)
    (hh : 0 < h) (hh1 : h ≤ 1) (_hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hcb : ∀ p, |c p| ≤ M) (hdb : ∀ p, |d p| ≤ M)
    (hsmall : B * (1 + heatConstant) * ProfileVolterra.powerConstant a * h ^ θ ≤ 1 / 2)
    (hvol : ∀ t ∈ Ioc 0 h, ∀ x,
      |c (t, x) - d (t, x)| ≤ A * t ^ a + B * t ^ b *
        |varianceMap c t x - varianceMap d t x|) :
    ∀ t ∈ Ioc 0 h, ∀ x, |c (t, x) - d (t, x)| ≤ 2 * A * t ^ a := by
  let V : Set ℝ := {v | ∃ t ∈ Ioc 0 h, ∃ x : HeatCircle,
    v = t ^ (-a) * |c (t, x) - d (t, x)|}
  have hV : V.Nonempty := ⟨h ^ (-a) * |c (h, 0) - d (h, 0)|, h, ⟨hh, le_rfl⟩, 0, rfl⟩
  have hVb : BddAbove V := by
    refine ⟨2 * M, ?_⟩
    rintro v ⟨t, ht, x, rfl⟩
    have hw : t ^ (-a) ≤ 1 := Real.rpow_le_one ht.1.le (ht.2.trans hh1) (by linarith)
    have hdif : |c (t, x) - d (t, x)| ≤ 2 * M :=
      (abs_sub _ _).trans (by linarith [hcb (t, x), hdb (t, x)])
    exact (mul_le_mul_of_nonneg_right hw (abs_nonneg _)).trans (by simpa using hdif)
  let S := sSup V
  have hS : 0 ≤ S := (mul_nonneg (Real.rpow_nonneg hh.le _) (abs_nonneg _)).trans
    (le_csSup hVb (show h ^ (-a) * |c (h, 0) - d (h, 0)| ∈ V from
      ⟨h, ⟨hh, le_rfl⟩, 0, rfl⟩))
  have hweight : ∀ t ∈ Ioc 0 h, ∀ x, |c (t, x) - d (t, x)| ≤ S * t ^ a := by
    intro t ht x
    have hv : t ^ (-a) * |c (t, x) - d (t, x)| ≤ S :=
      le_csSup hVb ⟨t, ht, x, rfl⟩
    have he := mul_le_mul_of_nonneg_right hv (Real.rpow_nonneg ht.1.le a)
    have hp : t ^ (-a) * t ^ a = 1 := by
      rw [← Real.rpow_add ht.1, neg_add_cancel, Real.rpow_zero]
    calc
      _ = (t ^ (-a) * |c (t, x) - d (t, x)|) * t ^ a := by rw [mul_right_comm, hp, one_mul]
      _ ≤ _ := he
  have hK : 0 ≤ ProfileVolterra.powerConstant a := (ProfileVolterra.powerConstant_pos ha).le
  have hHC : 0 ≤ 1 + heatConstant := by linarith [heatConstant_pos]
  have hentry : ∀ t ∈ Ioc 0 h, ∀ x,
      t ^ (-a) * |c (t, x) - d (t, x)| ≤
        A + (B * (1 + heatConstant) * ProfileVolterra.powerConstant a * h ^ θ) * S := by
    intro t ht x
    have hvc := varianceMap_sub hc hd ht.1 (ht.2.trans hh1) hM
      (fun _ _ _ => hcb _) (fun _ _ _ => hdb _) x
    have hv := varianceMap_weighted_bound (hc.sub hd) ht.1 (ht.2.trans hh1)
      (show 0 ≤ 2 * M by positivity) hS ha
      (fun u _ y => (abs_sub _ _).trans (by linarith [hcb (u, y), hdb (u, y)]))
      (fun u hu y => hweight u ⟨hu.1, hu.2.le.trans ht.2⟩ y) x
    rw [hvc] at hv
    have he := mul_le_mul_of_nonneg_left (hvol t ht x) (Real.rpow_nonneg ht.1.le (-a))
    have hm := mul_le_mul_of_nonneg_left hv
      (mul_nonneg hB (Real.rpow_nonneg ht.1.le b))
    have hm' := mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg ht.1.le (-a))
    have hp : t ^ (-a) * (A * t ^ a) = A := by
      rw [mul_left_comm, ← Real.rpow_add ht.1, neg_add_cancel, Real.rpow_zero, mul_one]
    have hprod : t ^ (-a) * (B * t ^ b * ((1 + heatConstant) * S *
        ProfileVolterra.powerConstant a * t ^ (a + 1 / 2))) =
        (B * (1 + heatConstant) * ProfileVolterra.powerConstant a * t ^ θ) * S := by
      calc
        _ = (B * (1 + heatConstant) * ProfileVolterra.powerConstant a) * S *
            (t ^ (-a) * t ^ b * t ^ (a + 1 / 2)) := by ring
        _ = _ := by
          rw [← Real.rpow_add ht.1, ← Real.rpow_add ht.1,
            show -a + b + (a + 1 / 2) = θ by linarith]
          ring
    have htθ : t ^ θ ≤ h ^ θ := Real.rpow_le_rpow ht.1.le ht.2 hθ.le
    calc
      _ ≤ A + t ^ (-a) * (B * t ^ b * ((1 + heatConstant) * S *
          ProfileVolterra.powerConstant a * t ^ (a + 1 / 2))) := by
        rw [mul_add, hp] at he
        linarith
      _ = A + (B * (1 + heatConstant) * ProfileVolterra.powerConstant a * t ^ θ) * S := by rw [hprod]
      _ ≤ _ := by gcongr
  have hsup : S ≤ A + (B * (1 + heatConstant) * ProfileVolterra.powerConstant a * h ^ θ) * S := by
    apply csSup_le hV
    rintro v ⟨t, ht, x, rfl⟩
    exact hentry t ht x
  have hSb : S ≤ 2 * A := by nlinarith [mul_le_mul_of_nonneg_right hsmall hS]
  intro t ht x
  exact (hweight t ht x).trans (mul_le_mul_of_nonneg_right hSb (Real.rpow_nonneg ht.1.le a))

/-- Actual profiles are pointwise Lipschitz in their original L² input at
every positive time. This coarser spatial bound is suitable for domination
when differentiating a parameterized covariance integral. -/
theorem physical_profile_pointwise_stability {a : ℝ → ℝ} {c d : ℝ × HeatCircle → ℝ}
    {ell M Ua H β h : ℝ} (u v : CircleL2)
    (ha : Measurable a) (hc : Measurable c) (hd : Measurable d)
    (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hh : 0 < h) (hh1 : h ≤ 1) (haB : ∀ z, |a z| ≤ Ua)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hcb : ∀ p, ell ≤ c p ∧ c p ≤ M) (hdb : ∀ p, ell ≤ d p ∧ d p ≤ M)
    (hsmall : memoryConstant ell H β * ProfileVolterra.powerConstant ((β - 2) / 4) *
      h ^ (β / 4) ≤ 1 / 2)
    (hcf : ∀ r ∈ Ioc 0 h, ∀ x, c (r, x) = profileUpdate a (physicalHeatMean u) c r x)
    (hdf : ∀ r ∈ Ioc 0 h, ∀ x, d (r, x) = profileUpdate a (physicalHeatMean v) d r x) :
    ∀ r ∈ Ioc 0 h, ∀ x, |c (r, x) - d (r, x)| ≤
      2 * (meanConstant ell H β * Real.sqrt (1 + heatConstant) * ‖u - v‖) *
        r ^ ((β - 2) / 4) := by
  have hcb' : ∀ p, |c p| ≤ M := fun p => by
    rw [abs_of_nonneg (hell.le.trans (hcb p).1)]
    exact (hcb p).2
  have hdb' : ∀ p, |d p| ≤ M := fun p => by
    rw [abs_of_nonneg (hell.le.trans (hdb p).1)]
    exact (hdb p).2
  apply spatial_weighted_absorption (a := (β - 2) / 4) (b := (β - 2) / 4)
    (θ := β / 4) hc hd (by linarith) (by linarith) (by positivity) (by ring)
    hh hh1 (by positivity [meanConstant_nonneg (β := β) hell.le hH])
    (varianceConstant_nonneg hell.le hH) hM hcb' hdb'
    (by simpa only [memoryConstant, mul_assoc, mul_left_comm, mul_comm] using hsmall)
  intro r hr x
  rw [hcf r hr x, hdf r hr x]
  have he := profileUpdate_two_inputs (φ := physicalHeatMean u) (ψ := physicalHeatMean v)
    ha hc hd hell hM hH hβ.le hβ1 hr.1
    (hr.2.trans hh1) haB hholder
    (fun _ _ _ => (hcb _).1) (fun _ _ _ => (hcb _).2)
    (fun _ _ _ => (hdb _).1) (fun _ _ _ => (hdb _).2) x
  have hm := physicalHeatMean_pointwise hr.1 (hr.2.trans hh1) (u - v) x
  rw [← physicalHeatMean_difference hr.1] at hm
  have hp : r ^ ((β - 1) / 4) * r ^ (-(1 / 4 : ℝ)) = r ^ ((β - 2) / 4) := by
    rw [← Real.rpow_add hr.1]
    congr 1
    ring
  have hm' := mul_le_mul_of_nonneg_left hm
    (mul_nonneg (meanConstant_nonneg (β := β) hell.le hH)
      (Real.rpow_nonneg hr.1.le ((β - 1) / 4)))
  calc
    _ ≤ _ := he
    _ ≤ (meanConstant ell H β * r ^ ((β - 1) / 4)) *
        (Real.sqrt (1 + heatConstant) * r ^ (-(1 / 4 : ℝ)) * ‖u - v‖) +
        (varianceConstant ell H β * r ^ ((β - 2) / 4)) *
          |varianceMap c r x - varianceMap d r x| := add_le_add hm' le_rfl
    _ = _ := by
      have hmul : (meanConstant ell H β * r ^ ((β - 1) / 4)) *
          (Real.sqrt (1 + heatConstant) * r ^ (-(1 / 4 : ℝ)) * ‖u - v‖) =
          (meanConstant ell H β * Real.sqrt (1 + heatConstant) * ‖u - v‖) *
            r ^ ((β - 2) / 4) := by
        calc
          _ = (meanConstant ell H β * Real.sqrt (1 + heatConstant) * ‖u - v‖) *
              (r ^ ((β - 1) / 4) * r ^ (-(1 / 4 : ℝ))) := by ring
          _ = _ := by rw [hp]
      rw [hmul]

/-- The pointwise domination theorem applies to the actual canonical Borel
fixed point, with no choice of a parameter-dependent representative. -/
theorem canonical_profile_pointwise_stability [MeasurableSpace CircleL2] [BorelSpace CircleL2]
    {a : ℝ → ℝ} {ell M H β h : ℝ}
    (ha : Measurable a) (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hsmall : contractionConstant ell H β * h ^ (β / 4) ≤ 1 / 2)
    (hsmallPoint : memoryConstant ell H β * ProfileVolterra.powerConstant ((β - 2) / 4) *
      h ^ (β / 4) ≤ 1 / 2) (u v : CircleL2) :
    ∀ r ∈ Ioc 0 h, ∀ x,
      |CanonicalProfile.profile a ell h (u, (r, x)) -
        CanonicalProfile.profile a ell h (v, (r, x))| ≤
        2 * (meanConstant ell H β * Real.sqrt (1 + heatConstant) * ‖u - v‖) *
          r ^ ((β - 2) / 4) := by
  have hm := CanonicalProfile.profile_measurable ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall
  have hb := CanonicalProfile.profile_elliptic ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall
  have hf := CanonicalProfile.profile_fixed ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall
  have haB : ∀ z, |a z| ≤ M := by
    intro z
    rw [abs_of_nonneg (hell.le.trans (hal z))]
    exact hau z
  exact physical_profile_pointwise_stability u v ha
    (hm.comp (measurable_const.prodMk measurable_id)) (hm.comp (measurable_const.prodMk measurable_id))
    hell hM hH hβ hβ1 hh hh1 haB hholder (fun p => hb (u, p)) (fun p => hb (v, p))
    hsmallPoint (hf u) (hf v)

def inputLine (u d : CircleL2) (θ : ℝ) : CircleL2 := u + θ • d

theorem inputLine_sub (u d : CircleL2) (θ η : ℝ) :
    inputLine u d θ - inputLine u d η = (θ - η) • d := by
  simp only [inputLine, add_sub_add_left_eq_sub, sub_smul]

def pointwiseConstant (ell H β r : ℝ) (d : CircleL2) : ℝ :=
  2 * (meanConstant ell H β * Real.sqrt (1 + heatConstant) * ‖d‖) * r ^ ((β - 2) / 4)

theorem pointwiseConstant_nonneg {ell H β r : ℝ} (hell : 0 ≤ ell) (hH : 0 ≤ H)
    (hr : 0 ≤ r) (d : CircleL2) : 0 ≤ pointwiseConstant ell H β r d := by
  unfold pointwiseConstant
  positivity [meanConstant_nonneg (β := β) hell hH]

/-- Every positive-time scalar canonical profile curve is genuinely Lipschitz
in its real affine input parameter. Its constant is proportional to the norm
of the one signed spatial input. -/
theorem canonical_profile_line_lipschitz [MeasurableSpace CircleL2] [BorelSpace CircleL2]
    {a : ℝ → ℝ} {ell M H β h : ℝ}
    (ha : Measurable a) (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hsmall : contractionConstant ell H β * h ^ (β / 4) ≤ 1 / 2)
    (hsmallPoint : memoryConstant ell H β * ProfileVolterra.powerConstant ((β - 2) / 4) *
      h ^ (β / 4) ≤ 1 / 2) (u d : CircleL2) (r : ℝ) (hr : r ∈ Ioc 0 h) (x : HeatCircle) :
    LipschitzWith ⟨pointwiseConstant ell H β r d,
      pointwiseConstant_nonneg hell.le hH hr.1.le d⟩
      (fun θ : ℝ => CanonicalProfile.profile a ell h (inputLine u d θ, (r, x))) := by
  apply LipschitzWith.of_dist_le_mul
  intro θ η
  have he := canonical_profile_pointwise_stability ha hell hM hH hβ hβ1 hh hh1 hal hau
    hholder hsmall hsmallPoint (inputLine u d θ) (inputLine u d η) r hr x
  rw [inputLine_sub, norm_smul, Real.norm_eq_abs] at he
  change |CanonicalProfile.profile a ell h (inputLine u d θ, (r, x)) -
    CanonicalProfile.profile a ell h (inputLine u d η, (r, x))| ≤
      pointwiseConstant ell H β r d * |θ - η|
  simpa only [pointwiseConstant, mul_assoc, mul_left_comm, mul_comm] using he

end SHE.ProfilePointwise
