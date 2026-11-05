module

public import SHE.ControlledStoppedLeaf

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.StoppedAssignedLeaf
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks
  GaussianCenteredLeafMoments ControlledOldIntervals OldIntervalCovariance ControlledAssignedLeaf
  StoppedGaussianFeatures StoppedFourier ProfileVariance GaussianAudit JointGaussianBlocks
open scoped BigOperators
local instance : Fact (0 < 2 * π) := ⟨by positivity⟩
variable {n r k : ℕ}

def constant (P : CanonicalCovariance.ProfileParameters) (p : ℕ)
    (choices : List (Fin r × Fin k)) (factor : Fin k) : ℝ :=
  if block choices factor = [] then leafMomentConstant p P.exponent
  else gaussianAbsMoment (((2*p : ℕ) : ℝ)*P.exponent)

def scale (P : CanonicalCovariance.ProfileParameters) (choices : List (Fin r × Fin k)) (factor : Fin k)
    (lo hi : Fin r → ℝ) (age : ℝ) (chosen : block choices factor ≠ [] → Fin r) : ℝ :=
  if h : block choices factor = [] then P.holder*(upperConstant*P.upper)^(P.exponent/2)*age^(P.exponent/4)
  else (2 : ℝ)^((block choices factor).length-1)*P.holder*(upperConstant*(P.lower/2))^(P.exponent/2)*
    (hi (chosen h)-lo (chosen h))^(P.exponent/4)

theorem constant_nonneg (P : CanonicalCovariance.ProfileParameters) (p : ℕ)
    (choices : List (Fin r × Fin k)) (factor : Fin k) : 0 ≤ constant P p choices factor := by
  unfold constant
  split_ifs
  · exact leafMomentConstant_nonneg _ _
  · exact gaussianAbsMoment_nonneg _

theorem scale_nonneg (P : CanonicalCovariance.ProfileParameters)
    (choices : List (Fin r × Fin k)) (factor : Fin k) (lo hi : Fin r → ℝ)
    (hgap : ∀ j, lo j ≤ hi j) {age : ℝ} (hage : 0 ≤ age)
    (chosen : block choices factor ≠ [] → Fin r) : 0 ≤ scale P choices factor lo hi age chosen := by
  unfold scale
  split_ifs with h
  · exact mul_nonneg (mul_nonneg P.holder_nonneg
      (rpow_nonneg (mul_nonneg upperConstant_pos.le P.upper_nonneg) _)) (rpow_nonneg hage _)
  · exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) P.holder_nonneg)
      (rpow_nonneg (mul_nonneg upperConstant_pos.le (half_pos P.lower_pos).le) _))
      (rpow_nonneg (sub_nonneg.mpr (hgap (chosen h))) _)

/-- The actual canonical leaf block, with native leaf coordinate only.
Every original root stop/target is retained. The minimum assigned gap can
be selected arbitrarily for a nonempty block. -/
theorem leaf_even_moment (P : CanonicalCovariance.ProfileParameters)
    (Λ : ℝ) (u d : CircleL2) (θ : ℝ) (lo hi : Fin r → ℝ)
    (hdisjoint : ∀ j l, j ≠ l → hi j ≤ lo l ∨ hi l ≤ lo j)
    (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hσ : ∀ i, 0 < σ i) (hσ1 : ∀ i, σ i ≤ 1) (hages : ∀ i, σ i ≤ target i)
    (hlo : ∀ j, 0 ≤ lo j) (hgap : ∀ j, lo j < hi j)
    (hstop : ∀ j i, σ i ≤ lo j ∨ hi j ≤ σ i)
    (m : State n) (coordinate : Fin n) (hnative : σ coordinate = target coordinate)
    (ht : target coordinate ∈ Ioc 0 P.horizon)
    (hm : m coordinate = ControlledProfile.mean Λ u d (θ,(target coordinate,center coordinate)))
    (choices : List (Fin r × Fin k)) (hnd : (choices.map Prod.fst).Nodup) (factor : Fin k)
    (chosen : block choices factor ≠ [] → Fin r)
    (hchosen : ∀ h, chosen h ∈ block choices factor) (p : ℕ) :
    let A := familyCovariance σ target center (referenceProfile P Λ u d) lo hi
    let B := ControlledFixedReserve.covariance P Λ u d (fixedProfile P Λ u d lo hi)
      σ target center 0 θ
    let μ := (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
      (multivariateGaussian (0 : State n) B)
    let F := leaf choices factor P.coefficient m coordinate
      (ControlledProfile.profile P Λ u d (θ,(target coordinate,center coordinate)))
    Integrable (fun x => |F x|^(2*p)) μ ∧
      (∫ x, |F x|^(2*p) ∂μ) ≤ constant P p choices factor*
        (scale P choices factor lo hi (target coordinate) chosen)^(2*p) := by
  intro A B μ F
  by_cases hblock : block choices factor = []
  · have he : F = fun x : (Fin r → State n) × State n =>
        P.coefficient (m coordinate + ((∑ j, suppress (suppressed choices factor) x.1 j) + x.2) coordinate) -
          ControlledProfile.profile P Λ u d (θ,(target coordinate,center coordinate)) := by
      funext x
      exact leaf_empty choices factor hblock _ _ _ _ x
    rw [he]
    simpa only [constant, scale, hblock, dite_true, ite_true] using
      ControlledStoppedLeaf.native_leaf_even_moment P Λ u d θ lo hi hdisjoint σ target center hages
        coordinate hnative ht m hm (suppressed choices factor) p
  · rw [show F = jointBlock choices factor P.coefficient (fun y => m coordinate+y coordinate)
        (fun _ => EuclideanSpace.proj (𝕜 := ℝ) coordinate) from leaf_nonempty choices factor hblock _ _ _ _]
    have hh := PhysicalJointBlocks.rough_block_even_moment σ target center hσ hσ1 hages _
      (referenceProfile_measurable P Λ u d)
      (fun q => ⟨(mul_nonneg (fraction_pos P).le P.lower_pos.le).trans (referenceProfile_bounds P Λ u d q).1,
        (referenceProfile_bounds P Λ u d q).2⟩) lo hi hlo hgap hstop B choices hnd factor
      (chosen hblock) (hchosen hblock) coordinate P.coefficient P.measurable P.holder_nonneg
      P.exponent_pos.le P.holder_bound (fun y => m coordinate+y coordinate) (by fun_prop) p
    simpa only [constant, scale, hblock, dite_false, ite_false] using hh

end SHE.StoppedAssignedLeaf
