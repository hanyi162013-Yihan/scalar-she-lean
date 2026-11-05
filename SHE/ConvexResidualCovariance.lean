module

public import SHE.BoundedWindowDecomposition
public import SHE.ControlledFixedReserve

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ConvexResidualCovariance
open Set MeasureTheory ProbabilityTheory GaussianIncrement StoppedGaussianFeatures
  StoppedFourier ControlledOldIntervals
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {n r : ℕ}

/-- The old fractions are held fixed through the entire covariance segment.
The convex future law need not be a third profile fixed point. -/
theorem coefficient (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ)
    (u d : CircleL2) (lo hi : Fin r → ℝ) (θ η ζ : ℝ) :
    BoundedWindowDecomposition.residual P Λ u d lo hi
        (BoundedWindowDecomposition.convexProfile P Λ u d θ η ζ) =
      fun p => (1 - ζ) * ControlledFixedReserve.coefficient P Λ u d
          (fixedProfile P Λ u d lo hi) θ p +
        ζ * ControlledFixedReserve.coefficient P Λ u d
          (fixedProfile P Λ u d lo hi) η p := by
  funext p
  simp only [BoundedWindowDecomposition.residual,
    BoundedWindowDecomposition.convexProfile, ControlledFixedReserve.coefficient]
  ring

/-- Exact equality of the real profile interpolation covariance and the
matrix segment used by the Gaussian finite-difference formula. -/
theorem covariance (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ)
    (u d : CircleL2) (lo hi : Fin r → ℝ)
    (hdisjoint : ∀ j k, j ≠ k → hi j ≤ lo k ∨ hi k ≤ lo j)
    (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (q θ η ζ : ℝ) :
    stoppedCovariance σ target center
        (BoundedWindowDecomposition.residual P Λ u d lo hi
          (BoundedWindowDecomposition.convexProfile P Λ u d θ η ζ)) q =
      (1 - ζ) • ControlledFixedReserve.covariance P Λ u d
          (fixedProfile P Λ u d lo hi) σ target center q θ +
        ζ • ControlledFixedReserve.covariance P Λ u d
          (fixedProfile P Λ u d lo hi) σ target center q η := by
  have hm (a : ℝ) : Measurable (ControlledFixedReserve.coefficient P Λ u d
      (fixedProfile P Λ u d lo hi) a) := by
    exact ((ControlledProfile.profile_measurable P Λ u d).comp
      (measurable_const.prodMk measurable_id)).sub
        (fixedProfile_measurable P Λ u d lo hi)
  have hb (a : ℝ) (p : StoppedGaussianFeatures.Domain) :
      |ControlledFixedReserve.coefficient P Λ u d (fixedProfile P Λ u d lo hi) a p| ≤
        P.upper := by
    have h := BoundedWindowDecomposition.residual_bounds P Λ u d lo hi hdisjoint
      (fun z => ControlledProfile.profile P Λ u d (a, z))
      (fun z => ControlledProfile.profile_bounds P Λ u d (a, z)) p
    have h0 := (half_pos P.lower_pos).le.trans h.1
    change |BoundedWindowDecomposition.residual P Λ u d lo hi
      (fun z => ControlledProfile.profile P Λ u d (a, z)) p| ≤ P.upper
    rw [abs_of_nonneg h0]
    exact h.2
  rw [coefficient P Λ u d lo hi θ η ζ,
    StoppedCovarianceSplit.covariance_add σ target center hages q
      ((hm θ).const_mul (1 - ζ)) ((hm η).const_mul ζ)
      (fun p => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hb θ p) (abs_nonneg _))
      (fun p => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hb η p) (abs_nonneg _)),
    StoppedCovarianceSplit.covariance_const_mul,
    StoppedCovarianceSplit.covariance_const_mul]
  rfl

end SHE.ConvexResidualCovariance
