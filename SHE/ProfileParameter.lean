module

public import SHE.ProfilePointwise
public import SHE.MeasuredRealCurves
public import SHE.CanonicalProfileL2

@[expose] public section
set_option autoImplicit false

/-! Actual parameter derivatives of the canonical scalar profile. Spatially
uniform domination and the sharper spatial L² estimates are kept distinct. -/
noncomputable section
namespace SHE.ProfileParameter
open Set MeasureTheory AddCircle StoppedFourier ProfileVariance GaussianProfile
open ProfileL2 ProfileStability PhysicalProfile ProfilePointwise
open scoped NNReal Topology

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

abbrev Domain := ℝ × HeatCircle

/-- The actual canonical profile on its positive time window, extended by the
fixed elliptic baseline elsewhere. This extension makes every real parameter
curve continuous without imposing any auxiliary spatial continuity. -/
def profileCurve (a : ℝ → ℝ) (ell h : ℝ) (u d : CircleL2) (p : Domain) (θ : ℝ) : ℝ :=
  if p.1 ∈ Ioc 0 h then CanonicalProfile.profile a ell h (inputLine u d θ, p) else ell

def curveBound (ell H β h : ℝ) (d : CircleL2) (p : Domain) : ℝ :=
  if p.1 ∈ Ioc 0 h then pointwiseConstant ell H β p.1 d else 0

/-- The derivative is the ordinary scalar derivative, rather than an
unidentified limit or a supplied variation field. -/
def profileDerivative (a : ℝ → ℝ) (ell h : ℝ) (u d : CircleL2) (p : Domain × ℝ) : ℝ :=
  deriv (profileCurve a ell h u d p.1) p.2

theorem curveBound_nonneg {ell H β h : ℝ} (hell : 0 ≤ ell) (hH : 0 ≤ H)
    (d : CircleL2) (p : Domain) : 0 ≤ curveBound ell H β h d p := by
  unfold curveBound
  split_ifs with hr
  · exact pointwiseConstant_nonneg hell hH hr.1.le d
  · exact le_rfl

theorem profileCurve_eq {a : ℝ → ℝ} {ell h : ℝ} (u d : CircleL2)
    {r : ℝ} (hr : r ∈ Ioc 0 h) (x : HeatCircle) (θ : ℝ) :
    profileCurve a ell h u d (r, x) θ =
      CanonicalProfile.profile a ell h (inputLine u d θ, (r, x)) := by
  simp only [profileCurve, hr, ite_true]

theorem curveBound_eq {ell H β h : ℝ} (d : CircleL2)
    {r : ℝ} (hr : r ∈ Ioc 0 h) (x : HeatCircle) :
    curveBound ell H β h d (r, x) = pointwiseConstant ell H β r d := by
  simp only [curveBound, hr, ite_true]

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

include ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall

theorem profileCurve_measurable (u d : CircleL2) :
    Measurable (profileCurve a ell h u d).uncurry := by
  have hm := CanonicalProfile.profile_measurable ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall
  have hs : Measurable (fun p : Domain × ℝ => (inputLine u d p.2, p.1)) := by
    have hc : Continuous (inputLine u d) := by unfold inputLine; fun_prop
    exact (hc.measurable.comp measurable_snd).prodMk measurable_fst
  exact (hm.comp hs).ite (measurableSet_Ioc.preimage measurable_fst.fst) measurable_const

include hsmallPoint

theorem profileCurve_lipschitz (u d : CircleL2) (p : Domain) :
    LipschitzWith ⟨curveBound ell H β h d p, curveBound_nonneg hell.le hH d p⟩
      (profileCurve a ell h u d p) := by
  apply LipschitzWith.of_dist_le_mul
  intro θ η
  change |profileCurve a ell h u d p θ - profileCurve a ell h u d p η| ≤
    curveBound ell H β h d p * |θ - η|
  by_cases hr : p.1 ∈ Ioc 0 h
  · have he := canonical_profile_line_lipschitz ha hell hM hH hβ hβ1 hh hh1 hal hau
      hholder hsmall hsmallPoint u d p.1 hr p.2
    have hed := he.dist_le_mul θ η
    change |CanonicalProfile.profile a ell h (inputLine u d θ, (p.1, p.2)) -
      CanonicalProfile.profile a ell h (inputLine u d η, (p.1, p.2))| ≤
      pointwiseConstant ell H β p.1 d * |θ - η| at hed
    simpa only [profileCurve, curveBound, hr, ite_true] using hed
  · simp only [profileCurve, curveBound, hr, ite_false, sub_self, abs_zero, zero_mul, le_refl]

/-- Actual joint measurability of the canonical parameter derivative. No
continuity in the spatial/time auxiliary variable is assumed. -/
theorem profileDerivative_measurable (u d : CircleL2) :
    Measurable (profileDerivative a ell h u d) :=
  MeasuredRealCurves.derivative_measurable
    (fun p => (profileCurve_lipschitz ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall hsmallPoint u d p).continuous)
    (profileCurve_measurable ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall u d)

/-- For almost every real input parameter, the actual scalar profile is
parameter differentiable at almost every physical space-time point. -/
theorem ae_profile_hasDerivAt (μ : Measure Domain) [SFinite μ] (u d : CircleL2) :
    ∀ᵐ θ ∂volume, ∀ᵐ p ∂μ,
      HasDerivAt (profileCurve a ell h u d p) (profileDerivative a ell h u d (p, θ)) θ :=
  MeasuredRealCurves.ae_ae_hasDerivAt μ
    (profileCurve_measurable ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall u d)
    (profileCurve_lipschitz ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall hsmallPoint u d)

/-- A deterministic weighted domination field for the actual derivative.
Its time exponent is deliberately coarser than the spatial L² estimate. -/
theorem profileDerivative_bound (u d : CircleL2) (p : Domain) (θ : ℝ) :
    |profileDerivative a ell h u d (p, θ)| ≤ curveBound ell H β h d p :=
  MeasuredRealCurves.derivative_bound
    (profileCurve_lipschitz ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall hsmallPoint u d) p θ

end Canonical
end SHE.ProfileParameter
