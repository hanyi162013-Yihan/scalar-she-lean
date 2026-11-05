module

public import SHE.MeasurableL2Field

@[expose] public section
set_option autoImplicit false

/-! The canonical scalar profile as an actual jointly Borel spatial L² field. -/
noncomputable section
namespace SHE.CanonicalProfileL2
open Set MeasureTheory AddCircle StoppedFourier ProfileL2 GaussianProfile ProfileStability
open MeasurableL2Field

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩

def profileField (a : ℝ → ℝ) (ell h : ℝ) (p : (CircleL2 × ℝ) × HeatCircle) : ℂ :=
  CanonicalProfile.profile a ell h (p.1.1, (p.1.2, p.2))

def l2Profile (a : ℝ → ℝ) (ell h : ℝ) : CircleL2 × ℝ → CircleL2 :=
  realizeL2 (ν := haarAddCircle) (profileField a ell h)

theorem profileField_measurable [MeasurableSpace CircleL2] [BorelSpace CircleL2]
    {a : ℝ → ℝ} {ell M H β h : ℝ}
    (ha : Measurable a) (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hsmall : contractionConstant ell H β * h ^ (β / 4) ≤ 1 / 2) :
    Measurable (profileField a ell h) := by
  have hm := CanonicalProfile.profile_measurable ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall
  have hmap : Measurable (fun p : (CircleL2 × ℝ) × HeatCircle => (p.1.1, (p.1.2, p.2))) := by fun_prop
  exact Complex.continuous_ofReal.measurable.comp (hm.comp hmap)

theorem profileField_memLp [MeasurableSpace CircleL2] [BorelSpace CircleL2]
    {a : ℝ → ℝ} {ell M H β h : ℝ}
    (ha : Measurable a) (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hsmall : contractionConstant ell H β * h ^ (β / 4) ≤ 1 / 2) (p : CircleL2 × ℝ) :
    MemLp (fun x => profileField a ell h (p, x)) 2 haarAddCircle := by
  have hm := (profileField_measurable ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall).comp
    (measurable_const.prodMk measurable_id : Measurable (fun x : HeatCircle => (p, x)))
  apply MemLp.of_bound hm.aestronglyMeasurable M
  filter_upwards with x
  have hb := CanonicalProfile.profile_elliptic ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall
    (p.1, (p.2, x))
  change ‖(CanonicalProfile.profile a ell h (p.1, (p.2, x)) : ℂ)‖ ≤ M
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hell.le.trans hb.1)]
  exact hb.2

theorem l2Profile_measurable [MeasurableSpace CircleL2] [BorelSpace CircleL2]
    {a : ℝ → ℝ} {ell M H β h : ℝ}
    (ha : Measurable a) (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hsmall : contractionConstant ell H β * h ^ (β / 4) ≤ 1 / 2) :
    Measurable (l2Profile a ell h) :=
  realizeL2_measurable (profileField_measurable ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall)
    (profileField_memLp ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall)

theorem l2Profile_ae [MeasurableSpace CircleL2] [BorelSpace CircleL2]
    {a : ℝ → ℝ} {ell M H β h : ℝ}
    (ha : Measurable a) (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hsmall : contractionConstant ell H β * h ^ (β / 4) ≤ 1 / 2) (p : CircleL2 × ℝ) :
    l2Profile a ell h p =ᵐ[haarAddCircle] (fun x =>
      (CanonicalProfile.profile a ell h (p.1, (p.2, x)) : ℂ)) :=
  realizeL2_ae (profileField a ell h)
    (profileField_memLp ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall) p

theorem l2Profile_real_elliptic [MeasurableSpace CircleL2] [BorelSpace CircleL2]
    {a : ℝ → ℝ} {ell M H β h : ℝ}
    (ha : Measurable a) (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hsmall : contractionConstant ell H β * h ^ (β / 4) ≤ 1 / 2) (p : CircleL2 × ℝ) :
    ∀ᵐ x ∂haarAddCircle, (l2Profile a ell h p x).im = 0 ∧
      ell ≤ (l2Profile a ell h p x).re ∧ (l2Profile a ell h p x).re ≤ M := by
  filter_upwards [l2Profile_ae ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall p] with x hx
  rw [hx]
  exact ⟨rfl, CanonicalProfile.profile_elliptic ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall _⟩

theorem l2Profile_diff_norm [MeasurableSpace CircleL2] [BorelSpace CircleL2]
    {a : ℝ → ℝ} {ell M H β h : ℝ}
    (ha : Measurable a) (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hsmall : contractionConstant ell H β * h ^ (β / 4) ≤ 1 / 2) (u v : CircleL2) (r : ℝ) :
    ‖l2Profile a ell h (u, r) - l2Profile a ell h (v, r)‖ =
      normTwo haarAddCircle (fun x => CanonicalProfile.profile a ell h (u, (r, x)) -
        CanonicalProfile.profile a ell h (v, (r, x))) :=
  real_l2_diff_norm (l2Profile_ae ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall (u, r))
    (l2Profile_ae ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall (v, r))

theorem l2Profile_stability [MeasurableSpace CircleL2] [BorelSpace CircleL2]
    {a : ℝ → ℝ} {ell M H β h : ℝ}
    (ha : Measurable a) (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hsmall : contractionConstant ell H β * h ^ (β / 4) ≤ 1 / 2)
    (hsmallL2 : memoryConstant ell H β * ProfileVolterra.powerConstant ((β - 1) / 4) *
      h ^ (β / 4) ≤ 1 / 2) (u v : CircleL2) (r : ℝ) (hr : r ∈ Ioc 0 h) :
    ‖l2Profile a ell h (u, r) - l2Profile a ell h (v, r)‖ ≤
      2 * (meanConstant ell H β * ‖u - v‖) * r ^ ((β - 1) / 4) := by
  rw [l2Profile_diff_norm ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall]
  exact CanonicalProfile.profile_l2_stability ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall hsmallL2 u v r hr

end SHE.CanonicalProfileL2
