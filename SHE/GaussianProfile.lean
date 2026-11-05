module

public import SHE.GaussianAudit
public import SHE.ProfileVariance

@[expose] public section
set_option autoImplicit false

/-! Actual scalar Gaussian profile covariance derivatives and contraction. -/
noncomputable section
namespace SHE.GaussianProfile
open Set MeasureTheory ProbabilityTheory GaussianAudit ProfileVariance
open scoped NNReal

def gaussianAverage (a : ℝ → ℝ) (m v : ℝ) : ℝ :=
  ∫ z : ℝ, a (m + z) ∂gaussianReal 0 v.toNNReal

def varianceDerivative (a : ℝ → ℝ) (m v : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ z : ℝ, a (m + z) * secondScore v.toNNReal z ∂gaussianReal 0 v.toNNReal

theorem gaussianAverage_hasDerivAt {a : ℝ → ℝ} (ha : Measurable a) {M v : ℝ}
    (hB : ∀ z, |a z| ≤ M) (hv : 0 < v) (m : ℝ) :
    HasDerivAt (gaussianAverage a m) (varianceDerivative a m v) v := by
  have hnv : v.toNNReal ≠ 0 := by exact_mod_cast (show (0 : ℝ) < v.toNNReal by simpa using hv).ne'
  have hd := hasDerivAt_gaussian_variance_integral v.toNNReal hnv
    (fun z => a (m + z)) (ha.comp (measurable_const.add measurable_id)) M (fun z => hB _)
  unfold gaussianAverage varianceDerivative
  simpa only [Real.coe_toNNReal v hv.le] using hd

theorem incrementMoment_nonneg (β : ℝ) : 0 ≤ secondScoreAbsIncrementMoment β :=
  integral_nonneg (fun _z => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (abs_nonneg _) _))

/-- The covariance derivative gains the actual Hölder increment before any
absolute Gaussian score estimate is used. -/
theorem varianceDerivative_holder_bound {a : ℝ → ℝ} (ha : Measurable a) {M H β v : ℝ}
    (hB : ∀ z, |a z| ≤ M) (_hH : 0 ≤ H) (hβ : 0 ≤ β) (hv : 0 < v)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β) (m : ℝ) :
    |varianceDerivative a m v| ≤
      (H / 2) * secondScoreAbsIncrementMoment β * v ^ (β / 2 - 1) := by
  let nv : ℝ≥0 := v.toNNReal
  have hnv : nv ≠ 0 := by exact_mod_cast (show (0 : ℝ) < nv by simpa [nv] using hv).ne'
  have hnvR : (nv : ℝ) = v := Real.coe_toNNReal v hv.le
  have hi : Integrable (fun z => secondScore nv z * a (m + z)) (gaussianReal 0 nv) := by
    apply (integrable_secondScore nv).mul_bdd (c := M)
    · exact (ha.comp (measurable_const.add measurable_id)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hB (m + z))
  have hic : Integrable (fun z => secondScore nv z * (a (m + z) - a m)) (gaussianReal 0 nv) := by
    apply (hi.sub ((integrable_secondScore nv).mul_const (a m))).congr
    filter_upwards with z
    change secondScore nv z * a (m + z) - secondScore nv z * a m =
      secondScore nv z * (a (m + z) - a m)
    ring
  have hmom := integrable_secondScore_abs_rpow nv β hβ
  have hb : ∀ z : ℝ, ‖secondScore nv z * (a (m + z) - a m)‖ ≤
      H * (|secondScore nv z| * |z| ^ β) := by
    intro z
    have hh := hholder (m + z) m
    rw [show m + z - m = z by ring] at hh
    rw [Real.norm_eq_abs, abs_mul]
    have he := mul_le_mul_of_nonneg_left hh (abs_nonneg (secondScore nv z))
    nlinarith
  have hscore : |∫ z, a (m + z) * secondScore nv z ∂gaussianReal 0 nv| ≤
      H * (((nv : ℝ) ^ (β / 2) / (nv : ℝ)) * secondScoreAbsIncrementMoment β) := by
    simp_rw [mul_comm (a (m + _))]
    rw [← secondScore_center_root nv a m hi, ← Real.norm_eq_abs]
    calc
      _ ≤ ∫ z, ‖secondScore nv z * (a (m + z) - a m)‖ ∂gaussianReal 0 nv := norm_integral_le_integral_norm _
      _ ≤ ∫ z, H * (|secondScore nv z| * |z| ^ β) ∂gaussianReal 0 nv :=
        integral_mono hic.norm (hmom.const_mul H) hb
      _ = _ := by rw [integral_const_mul, secondScore_abs_increment_moment nv hnv β hβ]
  have hp : v ^ (β / 2) / v = v ^ (β / 2 - 1) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hv]
    congr 1
  rw [hnvR, hp] at hscore
  unfold varianceDerivative
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have he := mul_le_mul_of_nonneg_left hscore (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  convert he using 1
  ring

/-- A uniform covariance Lipschitz bound on the actual positive Gaussian family. -/
theorem gaussianAverage_variance_lipschitz {a : ℝ → ℝ} (ha : Measurable a) {M H β lo v w : ℝ}
    (hB : ∀ z, |a z| ≤ M) (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ2 : β ≤ 2)
    (hlo : 0 < lo) (hv : lo ≤ v) (hw : lo ≤ w)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β) (m : ℝ) :
    |gaussianAverage a m v - gaussianAverage a m w| ≤
      ((H / 2) * secondScoreAbsIncrementMoment β * lo ^ (β / 2 - 1)) * |v - w| := by
  have hcoef : 0 ≤ (H / 2) * secondScoreAbsIncrementMoment β :=
    mul_nonneg (by positivity) (incrementMoment_nonneg β)
  have hd : ∀ x ∈ Ici lo, HasDerivWithinAt (gaussianAverage a m)
      (varianceDerivative a m x) (Ici lo) x := by
    intro x hx
    exact (gaussianAverage_hasDerivAt ha hB (hlo.trans_le hx) m).hasDerivWithinAt
  have hb : ∀ x ∈ Ici lo, ‖varianceDerivative a m x‖ ≤
      (H / 2) * secondScoreAbsIncrementMoment β * lo ^ (β / 2 - 1) := by
    intro x hx
    rw [Real.norm_eq_abs]
    exact (varianceDerivative_holder_bound ha hB hH hβ (hlo.trans_le hx) hholder m).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hlo hx (by linarith)) hcoef)
  have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Ici lo) hw hv
  simpa only [Real.norm_eq_abs] using he

theorem gaussianAverage_elliptic {a : ℝ → ℝ} (ha : Measurable a) {ell M : ℝ}
    (hell : 0 ≤ ell) (_hM : 0 ≤ M) (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M) (m v : ℝ) :
    ell ≤ gaussianAverage a m v ∧ gaussianAverage a m v ≤ M := by
  have hi : Integrable (fun z => a (m + z)) (gaussianReal 0 v.toNNReal) := by
    apply (integrable_const M).mono' (ha.comp (measurable_const.add measurable_id)).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => by
      change |a (m + z)| ≤ M
      rw [abs_of_nonneg (hell.trans (hal _))]
      exact hau _)
  have hlo := integral_mono (integrable_const ell) hi (fun z => hal (m + z))
  have hhi := integral_mono hi (integrable_const M) (fun z => hau (m + z))
  simp only [integral_const, probReal_univ, one_smul] at hlo hhi
  exact ⟨hlo, hhi⟩

def profileUpdate (a : ℝ → ℝ) (φ : ℝ × StoppedFourier.HeatCircle → ℝ)
    (c : ℝ × StoppedFourier.HeatCircle → ℝ) (r : ℝ) (x : StoppedFourier.HeatCircle) : ℝ :=
  gaussianAverage a (φ (r, x)) (varianceMap c r x)

def contractionConstant (ell H β : ℝ) : ℝ :=
  upperConstant * ((H / 2) * secondScoreAbsIncrementMoment β) *
    (lowerConstant * ell) ^ (β / 2 - 1)

theorem contractionConstant_nonneg {ell H β : ℝ} (hell : 0 ≤ ell) (hH : 0 ≤ H) :
    0 ≤ contractionConstant ell H β := by
  unfold contractionConstant
  exact mul_nonneg (mul_nonneg upperConstant_pos.le
    (mul_nonneg (by positivity) (incrementMoment_nonneg β)))
    (Real.rpow_nonneg (mul_nonneg lowerConstant_pos.le hell) _)

/-- The actual scalar Gaussian profile update contracts by `r^(β/4)`: the
physical covariance map and the Hölder covariance derivative are both proved. -/
theorem profileUpdate_contraction {a : ℝ → ℝ} (ha : Measurable a)
    {φ c d : ℝ × StoppedFourier.HeatCircle → ℝ} {r ell M Ua H β D : ℝ}
    (hc : Measurable c) (hd : Measurable d) (hr : 0 < r) (hr1 : r ≤ 1)
    (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ2 : β ≤ 2) (hD : 0 ≤ D)
    (haB : ∀ z, |a z| ≤ Ua) (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hcl : ∀ s ∈ Ioo 0 r, ∀ y, ell ≤ c (s, y))
    (hcu : ∀ s ∈ Ioo 0 r, ∀ y, c (s, y) ≤ M)
    (hdl : ∀ s ∈ Ioo 0 r, ∀ y, ell ≤ d (s, y))
    (hdu : ∀ s ∈ Ioo 0 r, ∀ y, d (s, y) ≤ M)
    (hcd : ∀ s ∈ Ioo 0 r, ∀ y, |c (s, y) - d (s, y)| ≤ D) (x : StoppedFourier.HeatCircle) :
    |profileUpdate a φ c r x - profileUpdate a φ d r x| ≤
      contractionConstant ell H β * r ^ (β / 4) * D := by
  have hvc := varianceMap_elliptic hc hr hr1 hell.le hM hcl hcu x
  have hvd := varianceMap_elliptic hd hr hr1 hell.le hM hdl hdu x
  have hcM : ∀ s ∈ Ioo 0 r, ∀ y, |c (s, y)| ≤ M := by
    intro s hs y
    rw [abs_of_nonneg (hell.le.trans (hcl s hs y))]
    exact hcu s hs y
  have hdM : ∀ s ∈ Ioo 0 r, ∀ y, |d (s, y)| ≤ M := by
    intro s hs y
    rw [abs_of_nonneg (hell.le.trans (hdl s hs y))]
    exact hdu s hs y
  have hvl := varianceMap_lipschitz hc hd hr hr1 hM hD hcM hdM hcd x
  have hlo : 0 < lowerConstant * ell * r ^ (1 / 2 : ℝ) :=
    mul_pos (mul_pos lowerConstant_pos hell) (Real.rpow_pos_of_pos hr _)
  have hg := gaussianAverage_variance_lipschitz ha haB hH hβ hβ2 hlo hvc.1 hvd.1 hholder (φ (r, x))
  have hcoef : 0 ≤ (H / 2) * secondScoreAbsIncrementMoment β *
      (lowerConstant * ell * r ^ (1 / 2 : ℝ)) ^ (β / 2 - 1) :=
    mul_nonneg (mul_nonneg (by positivity) (incrementMoment_nonneg β)) (Real.rpow_nonneg hlo.le _)
  have hb := hg.trans (mul_le_mul_of_nonneg_left hvl hcoef)
  have he : ((H / 2) * secondScoreAbsIncrementMoment β *
      (lowerConstant * ell * r ^ (1 / 2 : ℝ)) ^ (β / 2 - 1)) *
      (upperConstant * D * r ^ (1 / 2 : ℝ)) = contractionConstant ell H β * r ^ (β / 4) * D := by
    rw [Real.mul_rpow (mul_nonneg lowerConstant_pos.le hell.le) (Real.rpow_nonneg hr.le _)]
    calc
      _ = (upperConstant * ((H / 2) * secondScoreAbsIncrementMoment β) *
          (lowerConstant * ell) ^ (β / 2 - 1)) * D *
          ((r ^ (1 / 2 : ℝ)) ^ (β / 2 - 1) * r ^ (1 / 2 : ℝ)) := by ring
      _ = _ := by
        rw [← Real.rpow_mul hr.le, ← Real.rpow_add hr,
          show (1 / 2 : ℝ) * (β / 2 - 1) + 1 / 2 = β / 4 by ring]
        unfold contractionConstant
        ring
  exact hb.trans_eq he

theorem gaussianAverage_density {a : ℝ → ℝ} {v : ℝ} (hv : 0 < v) (m : ℝ) :
    gaussianAverage a m v = ∫ z : ℝ, a (m + z) * GaussianAudit.varianceDensity v z := by
  unfold gaussianAverage
  rw [integral_gaussianReal_eq_integral_smul (v := v.toNNReal) (by positivity)]
  apply integral_congr_ae
  filter_upwards with z
  rw [GaussianAudit.varianceDensity_eq_pdf hv, smul_eq_mul, mul_comm]

/-- Joint measurability uses the actual Gaussian density integral, including the
zero-variance branch, and requires only measurability of the bounded test. -/
theorem gaussianAverage_joint_measurable {a : ℝ → ℝ} (ha : Measurable a) :
    Measurable (fun p : ℝ × ℝ => gaussianAverage a p.1 p.2) := by
  classical
  have hd : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      a (p.1.1 + p.2) * GaussianAudit.varianceDensity p.1.2 p.2) := by
    have ha' : Measurable (fun p : (ℝ × ℝ) × ℝ => a (p.1.1 + p.2)) :=
      ha.comp ((measurable_fst.fst).add measurable_snd)
    have hg : Measurable (fun p : (ℝ × ℝ) × ℝ => GaussianAudit.varianceDensity p.1.2 p.2) := by
      unfold GaussianAudit.varianceDensity
      fun_prop
    exact ha'.mul hg
  have hi : Measurable (fun p : ℝ × ℝ => ∫ z : ℝ,
      a (p.1 + z) * GaussianAudit.varianceDensity p.2 z) :=
    hd.stronglyMeasurable.integral_prod_right.measurable
  have hset : MeasurableSet {p : ℝ × ℝ | 0 < p.2} :=
    measurableSet_lt measurable_const measurable_snd
  have hp : Measurable (fun p : ℝ × ℝ => if 0 < p.2 then
      (∫ z : ℝ, a (p.1 + z) * GaussianAudit.varianceDensity p.2 z) else a p.1) :=
    hi.ite hset (ha.comp measurable_fst)
  convert hp using 1
  funext p
  by_cases hv : 0 < p.2
  · rw [ite_eq_left hv, gaussianAverage_density hv]
  · rw [ite_eq_right hv]
    unfold gaussianAverage
    rw [Real.toNNReal_eq_zero.mpr (le_of_not_gt hv), gaussianReal_zero_var, integral_dirac]
    simp only [add_zero]

def positiveProfileUpdate (a : ℝ → ℝ) (φ c : ℝ × StoppedFourier.HeatCircle → ℝ)
    (p : ℝ × StoppedFourier.HeatCircle) : ℝ :=
  gaussianAverage a (φ p) (positiveVarianceMap c p)

theorem positiveProfileUpdate_measurable {a : ℝ → ℝ} {φ c : ℝ × StoppedFourier.HeatCircle → ℝ}
    (ha : Measurable a) (hφ : Measurable φ) (hc : Measurable c) :
    Measurable (positiveProfileUpdate a φ c) :=
  (gaussianAverage_joint_measurable ha).comp (hφ.prodMk (positiveVarianceMap_measurable hc))

theorem positiveProfileUpdate_eq {a : ℝ → ℝ} {φ c : ℝ × StoppedFourier.HeatCircle → ℝ}
    {r : ℝ} (hr : 0 ≤ r) (x : StoppedFourier.HeatCircle) :
    positiveProfileUpdate a φ c (r, x) = profileUpdate a φ c r x := by
  unfold positiveProfileUpdate profileUpdate
  rw [positiveVarianceMap_eq hr]

/-- Joint measurability of the genuine profile update on its entire nonnegative-time domain. -/
theorem profileUpdate_joint_measurable {a : ℝ → ℝ} {φ c : ℝ × StoppedFourier.HeatCircle → ℝ}
    (ha : Measurable a) (hφ : Measurable φ) (hc : Measurable c) :
    Measurable (fun p : {p : ℝ × StoppedFourier.HeatCircle // 0 ≤ p.1} =>
      profileUpdate a φ c p.val.1 p.val.2) := by
  have hm : Measurable (fun p : {p : ℝ × StoppedFourier.HeatCircle // 0 ≤ p.1} =>
      positiveProfileUpdate a φ c p.val) :=
    (positiveProfileUpdate_measurable ha hφ hc).comp measurable_subtype_coe
  convert hm using 1
  funext p
  exact (positiveProfileUpdate_eq p.property p.val.2).symm

theorem gaussianAverage_holder_displacement {a : ℝ → ℝ} (ha : Measurable a) {M H β v : ℝ}
    (hB : ∀ z, |a z| ≤ M) (_hH : 0 ≤ H) (hβ : 0 ≤ β) (hv : 0 ≤ v)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β) (m : ℝ) :
    |gaussianAverage a m v - a m| ≤ H * gaussianAbsMoment β * v ^ (β / 2) := by
  have hi : Integrable (fun z => a (m + z)) (gaussianReal 0 v.toNNReal) := by
    apply (integrable_const M).mono' (ha.comp (measurable_const.add measurable_id)).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => by change |a (m + z)| ≤ M; exact hB _)
  have hc : (∫ _z : ℝ, a m ∂gaussianReal 0 v.toNNReal) = a m := by simp
  unfold gaussianAverage
  rw [← hc, ← integral_sub hi (integrable_const _), ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ z : ℝ, ‖a (m + z) - a m‖ ∂gaussianReal 0 v.toNNReal := norm_integral_le_integral_norm _
    _ ≤ ∫ z : ℝ, H * |z| ^ β ∂gaussianReal 0 v.toNNReal := by
      apply integral_mono (hi.sub (integrable_const _)).norm
        ((integrable_gaussian_abs_rpow v.toNNReal β hβ).const_mul H)
      intro z
      change ‖a (m + z) - a m‖ ≤ H * |z| ^ β
      rw [Real.norm_eq_abs]
      simpa only [show m + z - m = z by ring] using hholder (m + z) m
    _ = _ := by
      rw [integral_const_mul, gaussian_abs_rpow_moment v.toNNReal β hβ, Real.coe_toNNReal v hv]
      ring

/-- The actual Gaussian profile update has the manuscript's `r^(β/4)`
displacement from the unsmoothed coefficient. -/
theorem profileUpdate_displacement {a : ℝ → ℝ} (ha : Measurable a)
    {φ c : ℝ × StoppedFourier.HeatCircle → ℝ} {r ell M Ua H β : ℝ}
    (hc : Measurable c) (hr : 0 < r) (hr1 : r ≤ 1) (hell : 0 < ell) (hM : 0 ≤ M)
    (hH : 0 ≤ H) (hβ : 0 ≤ β) (haB : ∀ z, |a z| ≤ Ua)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hcl : ∀ s ∈ Ioo 0 r, ∀ y, ell ≤ c (s, y))
    (hcu : ∀ s ∈ Ioo 0 r, ∀ y, c (s, y) ≤ M) (x : StoppedFourier.HeatCircle) :
    |profileUpdate a φ c r x - a (φ (r, x))| ≤
      H * gaussianAbsMoment β * (upperConstant * M) ^ (β / 2) * r ^ (β / 4) := by
  have hv := varianceMap_elliptic hc hr hr1 hell.le hM hcl hcu x
  have hv0 : 0 ≤ varianceMap c r x :=
    (mul_nonneg (mul_nonneg lowerConstant_pos.le hell.le) (Real.rpow_nonneg hr.le _)).trans hv.1
  have hg := gaussianAverage_holder_displacement ha haB hH hβ hv0 hholder (φ (r, x))
  have hp := Real.rpow_le_rpow hv0 hv.2 (show 0 ≤ β / 2 by positivity)
  have hh := mul_le_mul_of_nonneg_left hp (mul_nonneg hH (gaussianAbsMoment_nonneg β))
  have he : (H * gaussianAbsMoment β) * (upperConstant * M * r ^ (1 / 2 : ℝ)) ^ (β / 2) =
      H * gaussianAbsMoment β * (upperConstant * M) ^ (β / 2) * r ^ (β / 4) := by
    rw [Real.mul_rpow (mul_nonneg upperConstant_pos.le hM) (Real.rpow_nonneg hr.le _),
      ← Real.rpow_mul hr.le, show (1 / 2 : ℝ) * (β / 2) = β / 4 by ring]
    ring
  exact hg.trans (hh.trans_eq he)

end SHE.GaussianProfile
