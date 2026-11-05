module

public import SHE.ProfileParameter
public import SHE.RealCurveL2

@[expose] public section
set_option autoImplicit false

/-! Sharp one-input L² bounds for genuine canonical-profile parameter derivatives. -/
noncomputable section
namespace SHE.ProfileParameterL2
open Set MeasureTheory AddCircle StoppedFourier ProfileVariance GaussianProfile
open ProfileL2 ProfileStability PhysicalProfile ProfilePointwise ProfileParameter
open scoped NNReal Topology

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

section Canonical
variable [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable {a : ℝ → ℝ} {ell M H β h : ℝ}
variable (ha : Measurable a) (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H)
  (hβ : 0 < β) (hβ1 : β ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
  (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M)
  (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
  (hsmall : contractionConstant ell H β * h ^ (β / 4) ≤ 1 / 2)
  (hsmallPoint : memoryConstant ell H β * ProfileVolterra.powerConstant ((β - 2) / 4) *
    h ^ (β / 4) ≤ 1 / 2)
  (hsmallL2 : memoryConstant ell H β * ProfileVolterra.powerConstant ((β - 1) / 4) *
    h ^ (β / 4) ≤ 1 / 2)

include ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall hsmallPoint

theorem spatial_curve_lipschitz (u d : CircleL2) {r : ℝ} (hr : r ∈ Ioc 0 h) :
    ∀ x : HeatCircle, LipschitzWith ⟨pointwiseConstant ell H β r d,
      pointwiseConstant_nonneg hell.le hH hr.1.le d⟩ (profileCurve a ell h u d (r, x)) := by
  intro x
  have heq : profileCurve a ell h u d (r, x) = fun θ =>
      CanonicalProfile.profile a ell h (inputLine u d θ, (r, x)) := by
    funext θ
    exact profileCurve_eq u d hr x θ
  rw [heq]
  exact canonical_profile_line_lipschitz ha hell hM hH hβ hβ1 hh hh1 hal hau hholder
    hsmall hsmallPoint u d r hr x

include hsmallL2

/-- The sharp spatial L² constant of the exact canonical profile transfers to
its ordinary scalar derivative at every parameter where that derivative exists
a.e. in space. No derivative equation or profile-variation estimate is assumed. -/
theorem profileDerivative_l2_bound (u d : CircleL2) {r θ : ℝ} (hr : r ∈ Ioc 0 h)
    (hd : ∀ᵐ x ∂haarAddCircle, HasDerivAt (profileCurve a ell h u d (r, x))
      (profileDerivative a ell h u d ((r, x), θ)) θ) :
    MemLp (fun x => profileDerivative a ell h u d ((r, x), θ)) 2 haarAddCircle ∧
      normTwo haarAddCircle (fun x => profileDerivative a ell h u d ((r, x), θ)) ≤
        2 * (meanConstant ell H β * ‖d‖) * r ^ ((β - 1) / 4) := by
  have hm : Measurable (fun p : HeatCircle × ℝ => profileCurve a ell h u d (r, p.1) p.2) :=
    (profileCurve_measurable ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall u d).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  apply RealCurveL2.derivative_normTwo_bound haarAddCircle hm
    (spatial_curve_lipschitz ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall hsmallPoint u d hr)
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (mul_nonneg (meanConstant_nonneg (β := β) hell.le hH) (norm_nonneg d)))
      (Real.rpow_nonneg hr.1.le _))
    _ hd
  intro η ξ
  have he := CanonicalProfile.profile_l2_stability ha hell hM hH hβ hβ1 hh hh1 hal hau
    hholder hsmall hsmallL2 (inputLine u d η) (inputLine u d ξ) r hr
  rw [inputLine_sub, norm_smul, Real.norm_eq_abs] at he
  have heq : (fun x : HeatCircle => profileCurve a ell h u d (r, x) η -
      profileCurve a ell h u d (r, x) ξ) = fun x =>
      CanonicalProfile.profile a ell h (inputLine u d η, (r, x)) -
        CanonicalProfile.profile a ell h (inputLine u d ξ, (r, x)) := by
    funext x
    rw [profileCurve_eq u d hr x η, profileCurve_eq u d hr x ξ]
  rw [heq]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using he

/-- A single null set of real input parameters suffices for a.e. time and a.e.
space, with the sharp L² one-input gain retained at those times. -/
theorem ae_profileDerivative_l2 (u d : CircleL2) :
    ∀ᵐ θ ∂volume, ∀ᵐ r ∂volume.restrict (Ioc 0 h),
      MemLp (fun x => profileDerivative a ell h u d ((r, x), θ)) 2 haarAddCircle ∧
      normTwo haarAddCircle (fun x => profileDerivative a ell h u d ((r, x), θ)) ≤
        2 * (meanConstant ell H β * ‖d‖) * r ^ ((β - 1) / 4) := by
  have he := ae_profile_hasDerivAt ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall
    hsmallPoint ((volume.restrict (Ioc 0 h)).prod (haarAddCircle (T := 2 * Real.pi))) u d
  filter_upwards [he] with θ hθ
  filter_upwards [Measure.ae_ae_of_ae_prod hθ, ae_restrict_mem measurableSet_Ioc] with r hr hrmem
  exact profileDerivative_l2_bound ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall
    hsmallPoint hsmallL2 u d hrmem hr

end Canonical
end SHE.ProfileParameterL2
