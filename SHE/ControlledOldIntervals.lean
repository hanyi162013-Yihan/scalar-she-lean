module

public import SHE.OldIntervalSum

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ControlledOldIntervals
open Set MeasureTheory ProbabilityTheory AddCircle GaussianIncrement GaussianRangeSmooth
  StoppedGaussianFeatures StoppedFourier OldIntervalCovariance ControlledProfile ProfilePointwise ProfileStability
open scoped BigOperators Matrix.Norms.L2Operator
local instance controlledOldIntervals_periodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {n r : ℕ}

/-- A single fixed reference fraction for every old interval and every
interpolation parameter. Its total cost is half the scalar ellipticity floor. -/
def fraction (P : CanonicalCovariance.ProfileParameters) : ℝ := P.lower / (2 * P.upper)

def referenceProfile (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d : CircleL2)
    (p : ControlledProfile.Domain) : ℝ := fraction P * profile P Λ u d (0, p)

def fixedProfile (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d : CircleL2)
    (lo hi : Fin r → ℝ) : ControlledProfile.Domain → ℝ :=
  sumProfile (referenceProfile P Λ u d) lo hi

theorem upper_pos (P : CanonicalCovariance.ProfileParameters) : 0 < P.upper :=
  P.lower_pos.trans_le ((P.lower_bound 0).trans (P.upper_bound 0))

theorem fraction_pos (P : CanonicalCovariance.ProfileParameters) : 0 < fraction P :=
  div_pos P.lower_pos (mul_pos (by norm_num) (upper_pos P))

theorem fraction_mul_upper (P : CanonicalCovariance.ProfileParameters) : fraction P * P.upper = P.lower / 2 := by
  unfold fraction
  field_simp [(upper_pos P).ne']

theorem referenceProfile_measurable (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d : CircleL2) :
    Measurable (referenceProfile P Λ u d) :=
  measurable_const.mul ((profile_measurable P Λ u d).comp (measurable_const.prodMk measurable_id))

theorem referenceProfile_bounds (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d : CircleL2)
    (p : ControlledProfile.Domain) :
    fraction P * P.lower ≤ referenceProfile P Λ u d p ∧ referenceProfile P Λ u d p ≤ P.lower / 2 := by
  constructor
  · exact mul_le_mul_of_nonneg_left (profile_bounds P Λ u d (0, p)).1 (fraction_pos P).le
  · rw [← fraction_mul_upper P]
    exact mul_le_mul_of_nonneg_left (profile_bounds P Λ u d (0, p)).2 (fraction_pos P).le

theorem fixedProfile_measurable (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d : CircleL2)
    (lo hi : Fin r → ℝ) : Measurable (fixedProfile P Λ u d lo hi) :=
  measurable_sumProfile (referenceProfile_measurable P Λ u d) lo hi

theorem fixedProfile_bounds (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d : CircleL2)
    (lo hi : Fin r → ℝ) (hdisjoint : ∀ j k, j ≠ k → hi j ≤ lo k ∨ hi k ≤ lo j)
    (p : ControlledProfile.Domain) :
    0 ≤ fixedProfile P Λ u d lo hi p ∧ fixedProfile P Λ u d lo hi p ≤ P.lower / 2 := by
  have hnonneg (z : ControlledProfile.Domain) : 0 ≤ referenceProfile P Λ u d z :=
    (mul_nonneg (fraction_pos P).le P.lower_pos.le).trans (referenceProfile_bounds P Λ u d z).1
  have hh := sumProfile_bounds (referenceProfile P Λ u d) hnonneg lo hi hdisjoint p
  exact ⟨hh.1, hh.2.trans (referenceProfile_bounds P Λ u d p).2⟩

theorem residual_bounds (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d : CircleL2)
    (lo hi : Fin r → ℝ) (hdisjoint : ∀ j k, j ≠ k → hi j ≤ lo k ∨ hi k ≤ lo j)
    (θ : ℝ) (p : ControlledProfile.Domain) :
    P.lower / 2 ≤ profile P Λ u d (θ, p) - fixedProfile P Λ u d lo hi p ∧
      profile P Λ u d (θ, p) - fixedProfile P Λ u d lo hi p ≤ P.upper := by
  have hp := profile_bounds P Λ u d (θ, p)
  have ho := fixedProfile_bounds P Λ u d lo hi hdisjoint p
  constructor <;> linarith

/-- The actual fixed-reference old intervals and the positive residual
give the exact singular Gaussian split of the full controlled covariance. -/
theorem gaussian_split (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d : CircleL2)
    (lo hi : Fin r → ℝ) (hdisjoint : ∀ j k, j ≠ k → hi j ≤ lo k ∨ hi k ≤ lo j)
    (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (q θ : ℝ) :
    (multivariateGaussian (0 : State n) (stoppedCovariance σ target center (fixedProfile P Λ u d lo hi) q)) ∗
      multivariateGaussian 0 (ControlledFixedReserve.covariance P Λ u d (fixedProfile P Λ u d lo hi) σ target center q θ) =
      multivariateGaussian 0 (stoppedCovariance σ target center (fun p => profile P Λ u d (θ, p)) q) :=
  ControlledReservedWord.gaussian_split P Λ u d _ (fixedProfile_measurable P Λ u d lo hi)
    (show P.lower / 2 < P.lower by linarith [P.lower_pos])
    (fixedProfile_bounds P Λ u d lo hi hdisjoint) σ target center hages q θ

theorem covariance_sum (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d : CircleL2)
    (σ target : Fin n → ℝ) (center : Fin n → HeatCircle) (hages : ∀ i, σ i ≤ target i)
    (lo hi : Fin r → ℝ) :
    stoppedCovariance σ target center (fixedProfile P Λ u d lo hi) 0 =
      ∑ j, familyCovariance σ target center (referenceProfile P Λ u d) lo hi j := by
  apply covariance_sumProfile σ target center hages _ (referenceProfile_measurable P Λ u d) (M := P.lower / 2)
    (div_nonneg P.lower_pos.le (by norm_num))
  intro p
  rw [abs_of_nonneg ((mul_nonneg (fraction_pos P).le P.lower_pos.le).trans
    (referenceProfile_bounds P Λ u d p).1)]
  exact (referenceProfile_bounds P Λ u d p).2

end SHE.ControlledOldIntervals
