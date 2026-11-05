module

public import SHE.SmoothReferenceLimit
public import SHE.SmoothCylinderAlgebra

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.AdditiveProfile
open MeasureTheory ProbabilityTheory Set StoppedFourier GaussianProfile ProfileVariance
open CanonicalProfile
open scoped Topology

def totalCoefficient (m : ℝ) (a : ℝ → ℝ) (z : ℝ) : ℝ := m^2+a z
def additiveVariance (m r : ℝ) (x : HeatCircle) : ℝ := varianceMap (fun _ => m^2) r x

theorem additiveVariance_eq (m : ℝ) {r : ℝ} (hr : 0 ≤ r) (x : HeatCircle) :
    additiveVariance m r x=m^2*(∫ s in (0:ℝ)..r,‖circleHeat (r-s) x‖^2) := by
  unfold additiveVariance varianceMap
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_Ioo_of_le hr
  intro s hs
  unfold varianceDensity
  rw [integral_mul_const,heatPhysical_square_mass (sub_pos.mpr hs.2)]
  ring

theorem gaussianAverage_total (m : ℝ) {a : ℝ → ℝ} (ha : Measurable a) {M : ℝ}
    (hM : ∀ z,|a z| ≤ M) (mean v : ℝ) :
    gaussianAverage (totalCoefficient m a) mean v=m^2+gaussianAverage a mean v := by
  have hi : Integrable (fun z => a (mean+z)) (gaussianReal 0 v.toNNReal) := by
    apply (integrable_const M).mono' (ha.comp (measurable_const.add measurable_id)).aestronglyMeasurable
    exact ae_of_all _ (fun z => by change |a (mean+z)| ≤ M; exact hM _)
  change (∫ z,m^2+a (mean+z) ∂gaussianReal 0 v.toNNReal)=_
  rw [integral_add (integrable_const _) hi,integral_const,probReal_univ,one_smul]
  rfl

theorem insertion_cancellation (m : ℝ) (a : ℝ → ℝ) (c : ℝ × HeatCircle → ℝ)
    (z : ℝ) (p : ℝ × HeatCircle) :
    totalCoefficient m a z-(m^2+c p)=a z-c p := by unfold totalCoefficient; ring

theorem total_boundedSmooth (m : ℝ) {a : ℝ → ℝ} (ha : SmoothCylinders.BoundedSmooth a) :
    SmoothCylinders.BoundedSmooth (totalCoefficient m a) := by
  have hh := ha.sub (SmoothCylinders.BoundedSmooth.const (-(m^2)))
  convert hh using 1
  funext z
  simp only [totalCoefficient,sub_neg_eq_add,add_comm]

/-- The total canonical profile is used in physical covariance and Itô;
the residual profile is used in the independent common-Haar channel. -/
def residualProfile (m : ℝ) (a : ℝ → ℝ) (ell h : ℝ) (p : CircleL2 × ParametricProfile.Domain) : ℝ :=
  profile (totalCoefficient m a) (m^2+ell) h p-m^2

section Profile
variable {a : ℝ → ℝ} {ell M H β h m : ℝ}
variable (ha : Measurable a) (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hal : ∀ z,ell ≤ a z) (hau : ∀ z,a z ≤ M)
    (hholder : ∀ z w,|a z-a w| ≤ H*|z-w|^β)
    (hsmall : contractionConstant (m^2+ell) H β*h^(β/4) ≤ 1/2)

theorem total_measurable (ha : Measurable a) : Measurable (totalCoefficient m a) := measurable_const.add ha
theorem total_lower_pos (hell : 0 < ell) : 0 < m^2+ell := add_pos_of_nonneg_of_pos (sq_nonneg _) hell
theorem total_upper_nonneg (hM : 0 ≤ M) : 0 ≤ m^2+M := add_nonneg (sq_nonneg _) hM
theorem total_lower (hal : ∀ z,ell ≤ a z) (z : ℝ) : m^2+ell ≤ totalCoefficient m a z :=
  add_le_add le_rfl (hal z)
theorem total_upper (hau : ∀ z,a z ≤ M) (z : ℝ) : totalCoefficient m a z ≤ m^2+M :=
  add_le_add le_rfl (hau z)
theorem total_holder (hholder : ∀ z w,|a z-a w| ≤ H*|z-w|^β) (z w : ℝ) :
    |totalCoefficient m a z-totalCoefficient m a w| ≤ H*|z-w|^β := by
  simpa only [totalCoefficient,add_sub_add_left_eq_sub] using hholder z w

variable [MeasurableSpace CircleL2] [BorelSpace CircleL2]
include ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall

theorem residual_measurable : Measurable (residualProfile m a ell h) := by
  exact (profile_measurable (total_measurable ha) (total_lower_pos hell) (total_upper_nonneg hM)
    hH hβ hβ1 hh hh1 (total_lower hal) (total_upper hau) (total_holder hholder) hsmall).sub_const _

theorem residual_bounds (p : CircleL2 × ParametricProfile.Domain) :
    ell ≤ residualProfile m a ell h p ∧ residualProfile m a ell h p ≤ M := by
  have hb := profile_elliptic (total_measurable ha) (total_lower_pos hell) (total_upper_nonneg hM)
    hH hβ hβ1 hh hh1 (total_lower hal) (total_upper hau) (total_holder hholder) hsmall p
  change ell ≤ profile (totalCoefficient m a) (m^2+ell) h p-m^2 ∧
    profile (totalCoefficient m a) (m^2+ell) h p-m^2 ≤ M
  constructor <;> linarith [hb.1,hb.2]

theorem residual_fixed_total_variance (u : CircleL2) (r : ℝ) (hr : r ∈ Ioc 0 h) (x : HeatCircle) :
    residualProfile m a ell h (u,(r,x))=
      gaussianAverage a (PhysicalProfile.physicalHeatMean u (r,x))
        (varianceMap (fun q => profile (totalCoefficient m a) (m^2+ell) h (u,q)) r x) := by
  have he := profile_fixed (total_measurable ha) (total_lower_pos hell) (total_upper_nonneg hM)
    hH hβ hβ1 hh hh1 (total_lower hal) (total_upper hau) (total_holder hholder) hsmall u r hr x
  have haB : ∀ z,|a z| ≤ M := fun z => by rw [abs_of_nonneg (hell.le.trans (hal z))]; exact hau z
  change profile (totalCoefficient m a) (m^2+ell) h (u,(r,x))-m^2=_
  rw [he,profileUpdate,gaussianAverage_total m ha haB]
  ring

theorem variance_total_residual (u : CircleL2) {r : ℝ} (hr : 0 < r) (hrh : r ≤ h) (x : HeatCircle) :
    varianceMap (fun q => profile (totalCoefficient m a) (m^2+ell) h (u,q)) r x=
      additiveVariance m r x+varianceMap (fun q => residualProfile m a ell h (u,q)) r x := by
  have hm := profile_measurable (total_measurable ha) (total_lower_pos hell) (total_upper_nonneg hM)
    hH hβ hβ1 hh hh1 (total_lower hal) (total_upper hau) (total_holder hholder) hsmall
  have hb := profile_elliptic (total_measurable ha) (total_lower_pos hell) (total_upper_nonneg hM)
    hH hβ hβ1 hh hh1 (total_lower hal) (total_upper hau) (total_holder hholder) hsmall
  have hcm : Measurable (fun q : ParametricProfile.Domain =>
      profile (totalCoefficient m a) (m^2+ell) h (u,q)) :=
    hm.comp (measurable_const.prodMk measurable_id)
  have hdiff := varianceMap_sub
    (c := fun q => profile (totalCoefficient m a) (m^2+ell) h (u,q))
    (d := fun _ => m^2) (M := m^2+M) hcm measurable_const hr (hrh.trans hh1)
    (total_upper_nonneg (m := m) hM)
    (fun s _ y => by
      rw [abs_of_nonneg ((total_lower_pos hell).le.trans ((hb (u,(s,y))).1))]
      exact (hb (u,(s,y))).2)
    (fun _ _ _ => by rw [abs_of_nonneg (sq_nonneg m)]; exact le_add_of_nonneg_right hM) x
  change varianceMap (fun q => residualProfile m a ell h (u,q)) r x=
    varianceMap (fun q => profile (totalCoefficient m a) (m^2+ell) h (u,q)) r x-additiveVariance m r x at hdiff
  linarith

theorem residual_fixed (u : CircleL2) (r : ℝ) (hr : r ∈ Ioc 0 h) (x : HeatCircle) :
    residualProfile m a ell h (u,(r,x))=
      gaussianAverage a (PhysicalProfile.physicalHeatMean u (r,x))
        (additiveVariance m r x+varianceMap (fun q => residualProfile m a ell h (u,q)) r x) := by
  rw [residual_fixed_total_variance ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall u r hr x,
    variance_total_residual ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall u hr.1 hr.2 x]

end Profile
end SHE.AdditiveProfile
