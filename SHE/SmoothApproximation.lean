module

public import SHE.CompactMollifier
public import SHE.CanonicalCovariance

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.SmoothApproximation
open MeasureTheory ScalarReduction CompactMollifier
open scoped ContDiff Topology NNReal

theorem boundedSmooth_lipschitz {a : ℝ → ℝ} (ha : SmoothCylinders.BoundedSmooth a) :
    ∃ L : ℝ≥0,LipschitzWith L a := by
  obtain ⟨B,hB⟩ := ha.fderiv.norm_bound
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine ⟨⟨B,hB0⟩,lipschitzWith_of_nnnorm_fderiv_le
    (ha.smooth.differentiable (by simp)) (fun x => ?_)⟩
  exact_mod_cast hB x

/-- The bounded uniformly nondegenerate scalar hypothesis of the paper.
The sign of the original coefficient is unrestricted. -/
structure ScalarData where
  coefficient : ℝ → ℝ
  lower : ℝ
  upper : ℝ
  holder : ℝ
  exponent : ℝ
  lower_pos : 0 < lower
  holder_nonneg : 0 ≤ holder
  exponent_pos : 0 < exponent
  bounds : ∀ x,lower ≤ |coefficient x| ∧ |coefficient x| ≤ upper
  holder_bound : ∀ x y,|coefficient x-coefficient y| ≤ holder*|x-y|^exponent

namespace ScalarData
variable (D : ScalarData)

def beta : ℝ := workingExponent D.exponent
def ell : ℝ := D.lower^2/2
def cap : ℝ := D.upper^2
def holderConstant : ℝ := 2*D.upper*(D.holder+2*D.upper)
def residualCoefficient : ℝ → ℝ := residual D.coefficient D.lower
def smoothCoefficient (n : ℕ) : ℝ → ℝ := approximant D.residualCoefficient n

theorem upper_pos : 0 < D.upper := D.lower_pos.trans_le ((D.bounds 0).1.trans (D.bounds 0).2)
theorem beta_pos : 0 < D.beta := (workingExponent_admissible D.exponent_pos).1
theorem beta_le : D.beta ≤ 4/25 := (workingExponent_admissible D.exponent_pos).2.2
theorem beta_le_one : D.beta ≤ 1 := D.beta_le.trans (by norm_num)
theorem ell_pos : 0 < D.ell := div_pos (pow_pos D.lower_pos 2) (by norm_num)
theorem cap_nonneg : 0 ≤ D.cap := sq_nonneg _
theorem holderConstant_nonneg : 0 ≤ D.holderConstant := by
  unfold holderConstant
  exact mul_nonneg (mul_nonneg (by norm_num) D.upper_pos.le)
    (add_nonneg D.holder_nonneg (mul_nonneg (by norm_num) D.upper_pos.le))

theorem residual_bounds (x : ℝ) : D.ell ≤ D.residualCoefficient x ∧ D.residualCoefficient x ≤ D.cap :=
  residual_elliptic D.lower_pos D.bounds x

theorem residual_abs_bound (x : ℝ) : |D.residualCoefficient x| ≤ D.cap := by
  rw [abs_of_nonneg (D.ell_pos.le.trans (D.residual_bounds x).1)]
  exact (D.residual_bounds x).2

theorem residual_holder (x y : ℝ) :
    |D.residualCoefficient x-D.residualCoefficient y| ≤ D.holderConstant*|x-y|^D.beta := by
  exact ScalarReduction.residual_holder D.upper_pos.le
    (add_nonneg D.holder_nonneg (mul_nonneg (by norm_num) D.upper_pos.le))
    (fun z => (D.bounds z).2)
    (holder_exponent_reduction D.beta_pos (workingExponent_admissible D.exponent_pos).2.1
      D.holder_nonneg D.upper_pos.le (fun z => (D.bounds z).2) D.holder_bound) x y

theorem residual_continuous : Continuous D.residualCoefficient :=
  holder_continuous D.beta_pos D.holderConstant_nonneg D.residual_holder

theorem variance_split (x : ℝ) :
    (additiveAmplitude D.lower)^2+D.residualCoefficient x=(D.coefficient x)^2 :=
  residual_identity _ _ _

theorem smooth_boundedSmooth (n : ℕ) : SmoothCylinders.BoundedSmooth (D.smoothCoefficient n) :=
  approximant_boundedSmooth D.residual_continuous D.residual_abs_bound n

theorem smooth_bounds (n : ℕ) (x : ℝ) : D.ell ≤ D.smoothCoefficient n x ∧ D.smoothCoefficient n x ≤ D.cap :=
  approximant_elliptic D.residual_continuous D.ell_pos.le D.residual_bounds n x

theorem smooth_holder (n : ℕ) (x y : ℝ) :
    |D.smoothCoefficient n x-D.smoothCoefficient n y| ≤ D.holderConstant*|x-y|^D.beta :=
  approximant_holder D.residual_continuous D.residual_abs_bound D.residual_holder n x y

theorem smooth_lipschitz (n : ℕ) : ∃ L : ℝ≥0,LipschitzWith L (D.smoothCoefficient n) :=
  boundedSmooth_lipschitz (D.smooth_boundedSmooth n)

theorem smooth_uniform_limit : TendstoUniformly D.smoothCoefficient D.residualCoefficient Filter.atTop :=
  approximant_tendstoUniformly D.residual_continuous D.holderConstant_nonneg D.beta_pos D.residual_holder

theorem common_profile_horizon : ∃ h : ℝ,0 < h ∧ h ≤ 1 ∧
    GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*h^(D.beta/4) ≤ 1/2 :=
  ScalarProfileFixedPoint.exists_profile_horizon D.ell_pos.le D.holderConstant_nonneg D.beta_pos

/-- Every smooth approximation uses the same actual Gaussian profile
horizon and constants; no approximation-dependent ellipticity loss occurs. -/
def smoothProfileParameters (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hsmall : GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*h^(D.beta/4) ≤ 1/2)
    (n : ℕ) : CanonicalCovariance.ProfileParameters where
  coefficient := D.smoothCoefficient n
  lower := D.ell
  upper := D.cap
  holder := D.holderConstant
  exponent := D.beta
  horizon := h
  measurable := (D.smooth_boundedSmooth n).smooth.continuous.measurable
  lower_pos := D.ell_pos
  upper_nonneg := D.cap_nonneg
  holder_nonneg := D.holderConstant_nonneg
  exponent_pos := D.beta_pos
  exponent_le_one := D.beta_le_one
  horizon_pos := hh
  horizon_le_one := hh1
  lower_bound := fun z => (D.smooth_bounds n z).1
  upper_bound := fun z => (D.smooth_bounds n z).2
  holder_bound := D.smooth_holder n
  small := hsmall

def roughProfileParameters (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hsmall : GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*h^(D.beta/4) ≤ 1/2) :
    CanonicalCovariance.ProfileParameters where
  coefficient := D.residualCoefficient
  lower := D.ell
  upper := D.cap
  holder := D.holderConstant
  exponent := D.beta
  horizon := h
  measurable := D.residual_continuous.measurable
  lower_pos := D.ell_pos
  upper_nonneg := D.cap_nonneg
  holder_nonneg := D.holderConstant_nonneg
  exponent_pos := D.beta_pos
  exponent_le_one := D.beta_le_one
  horizon_pos := hh
  horizon_le_one := hh1
  lower_bound := fun z => (D.residual_bounds z).1
  upper_bound := fun z => (D.residual_bounds z).2
  holder_bound := D.residual_holder
  small := hsmall

end ScalarData
end SHE.SmoothApproximation
