module

public import SHE.ParametricProfile
public import SHE.CompatibleReference

@[expose] public section
set_option autoImplicit false

/-! Canonical physical scalar profile maps and measurable random inputs. -/
noncomputable section
namespace SHE.CanonicalProfile
open Set MeasureTheory AddCircle StoppedFourier ProfileVariance GaussianProfile ProfileL2 ProfileStability PhysicalProfile
open ParametricProfile

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

def profile (a : ℝ → ℝ) (ell h : ℝ) (p : CircleL2 × Domain) : ℝ :=
  canonicalProfile a (fun q => physicalHeatMean q.1 q.2) ell h p

theorem profile_measurable [MeasurableSpace CircleL2] [BorelSpace CircleL2]
    {a : ℝ → ℝ} {ell M H β h : ℝ}
    (ha : Measurable a) (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hsmall : contractionConstant ell H β * h ^ (β / 4) ≤ 1 / 2) :
    Measurable (profile a ell h) :=
  canonicalProfile_measurable ha physicalHeatMean_joint_measurable hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall

theorem profile_elliptic [MeasurableSpace CircleL2] [BorelSpace CircleL2]
    {a : ℝ → ℝ} {ell M H β h : ℝ}
    (ha : Measurable a) (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hsmall : contractionConstant ell H β * h ^ (β / 4) ≤ 1 / 2) (p : CircleL2 × Domain) :
    ell ≤ profile a ell h p ∧ profile a ell h p ≤ M :=
  canonicalProfile_elliptic ha physicalHeatMean_joint_measurable hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall p

theorem profile_fixed [MeasurableSpace CircleL2] [BorelSpace CircleL2]
    {a : ℝ → ℝ} {ell M H β h : ℝ}
    (ha : Measurable a) (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hsmall : contractionConstant ell H β * h ^ (β / 4) ≤ 1 / 2)
    (u : CircleL2) (r : ℝ) (hr : r ∈ Ioc 0 h) (x : HeatCircle) :
    profile a ell h (u, (r, x)) =
      profileUpdate a (physicalHeatMean u) (fun q => profile a ell h (u, q)) r x :=
  canonicalProfile_fixed ha physicalHeatMean_joint_measurable hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall u r hr x

/-- Substituting any measurable random L² state into the canonical physical
profile produces a jointly measurable future coefficient field. -/
theorem random_profile_measurable [MeasurableSpace CircleL2] [BorelSpace CircleL2]
    {Ω : Type*} [MeasurableSpace Ω] {U : Ω → CircleL2} (hU : Measurable U)
    {a : ℝ → ℝ} {ell M H β h : ℝ}
    (ha : Measurable a) (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hsmall : contractionConstant ell H β * h ^ (β / 4) ≤ 1 / 2) :
    Measurable (fun p : Ω × Domain => profile a ell h (U p.1, p.2)) :=
  (profile_measurable ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall).comp
    ((hU.comp measurable_fst).prodMk measurable_snd)

/-- Canonical profiles commute exactly with random-state substitution,
because their actual Picard iterates commute with substitution. -/
theorem random_profile_eq {Ω : Type*} (U : Ω → CircleL2) (a : ℝ → ℝ) (ell h : ℝ) (p : Ω × Domain) :
    canonicalProfile a (fun q => physicalHeatMean (U q.1) q.2) ell h p =
      profile a ell h (U p.1, p.2) :=
  canonicalProfile_comap a (fun q => physicalHeatMean q.1 q.2) ell h U p

theorem random_amplitude_measurable [MeasurableSpace CircleL2] [BorelSpace CircleL2]
    {Ω : Type*} [MeasurableSpace Ω] {U : Ω → CircleL2} (hU : Measurable U)
    {a : ℝ → ℝ} {ell M H β h : ℝ}
    (ha : Measurable a) (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hsmall : contractionConstant ell H β * h ^ (β / 4) ≤ 1 / 2) :
    Measurable (fun p : Ω × Domain => Real.sqrt (profile a ell h (U p.1, p.2))) :=
  (random_profile_measurable hU ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall).sqrt

/-- One-input L² stability for the actual canonical Borel profile map. -/
theorem profile_l2_stability [MeasurableSpace CircleL2] [BorelSpace CircleL2]
    {a : ℝ → ℝ} {ell M H β h : ℝ}
    (ha : Measurable a) (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hsmall : contractionConstant ell H β * h ^ (β / 4) ≤ 1 / 2)
    (hsmallL2 : memoryConstant ell H β * ProfileVolterra.powerConstant ((β - 1) / 4) *
      h ^ (β / 4) ≤ 1 / 2) (u v : CircleL2) :
    ∀ r ∈ Ioc 0 h,
      normTwo haarAddCircle (fun x => profile a ell h (u, (r, x)) - profile a ell h (v, (r, x))) ≤
        2 * (meanConstant ell H β * ‖u - v‖) * r ^ ((β - 1) / 4) := by
  have hm := profile_measurable ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall
  have hb := profile_elliptic ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall
  have hf := profile_fixed ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall
  have haB : ∀ z, |a z| ≤ M := by
    intro z
    rw [abs_of_nonneg (hell.le.trans (hal z))]
    exact hau z
  exact physical_profile_l2_stability u v ha
    (hm.comp (measurable_const.prodMk measurable_id)) (hm.comp (measurable_const.prodMk measurable_id))
    hell hM hH hβ hβ1 hh hh1 haB hholder (fun p => hb (u, p)) (fun p => hb (v, p))
    hsmallL2 (hf u) (hf v)

end SHE.CanonicalProfile
