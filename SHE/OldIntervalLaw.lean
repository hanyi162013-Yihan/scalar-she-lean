module

public import SHE.ControlledOldIntervals
public import SHE.GaussianFiniteSum

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1900000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ControlledOldIntervals
open Set MeasureTheory ProbabilityTheory AddCircle GaussianIncrement GaussianRangeSmooth
  StoppedGaussianFeatures StoppedFourier OldIntervalCovariance ControlledProfile
open scoped BigOperators
local instance oldIntervalLaw_periodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {n r : ℕ}

/-- Independent old physical interval vectors sum to exactly the fixed
reference old covariance used by the residual interpolation. -/
theorem old_sum_law (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d : CircleL2)
    (σ target : Fin n → ℝ) (center : Fin n → HeatCircle) (hages : ∀ i, σ i ≤ target i)
    (lo hi : Fin r → ℝ) :
    (Measure.pi (fun j => multivariateGaussian (0 : State n)
      (familyCovariance σ target center (referenceProfile P Λ u d) lo hi j))).map
      (fun y : Fin r → State n => ∑ j, y j) =
      multivariateGaussian 0 (stoppedCovariance σ target center (fixedProfile P Λ u d lo hi) 0) := by
  have hh := GaussianFiniteSum.map_sum r (familyCovariance σ target center (referenceProfile P Λ u d) lo hi)
    (fun j => covariance_posSemidef σ target center hages _
    (referenceProfile_measurable P Λ u d) (fun p =>
      ⟨(mul_nonneg (fraction_pos P).le P.lower_pos.le).trans (referenceProfile_bounds P Λ u d p).1,
        (referenceProfile_bounds P Λ u d p).2⟩) (lo j) (hi j))
  rw [hh, covariance_sum P Λ u d σ target center hages lo hi]

/-- The actual full controlled observation law is realized by the fixed
independent old interval vectors plus one varying residual vector. All old
covariances, coordinates and scores remain independent of the parameter. -/
theorem full_split_law (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d : CircleL2)
    (lo hi : Fin r → ℝ) (hdisjoint : ∀ j k, j ≠ k → hi j ≤ lo k ∨ hi k ≤ lo j)
    (σ target : Fin n → ℝ) (center : Fin n → HeatCircle) (hages : ∀ i, σ i ≤ target i) (θ : ℝ) :
    ((Measure.pi (fun j => multivariateGaussian (0 : State n)
      (familyCovariance σ target center (referenceProfile P Λ u d) lo hi j))).prod
      (multivariateGaussian (0 : State n) (ControlledFixedReserve.covariance P Λ u d
        (fixedProfile P Λ u d lo hi) σ target center 0 θ))).map
      (fun y : (Fin r → State n) × State n => (∑ j, y.1 j) + y.2) =
      multivariateGaussian 0 (stoppedCovariance σ target center (fun p => profile P Λ u d (θ, p)) 0) := by
  let μ := Measure.pi (fun j => multivariateGaussian (0 : State n)
    (familyCovariance σ target center (referenceProfile P Λ u d) lo hi j))
  let ν := multivariateGaussian (0 : State n) (ControlledFixedReserve.covariance P Λ u d
    (fixedProfile P Λ u d lo hi) σ target center 0 θ)
  have hprod : (μ.prod ν).map (fun y : (Fin r → State n) × State n => (∑ j, y.1 j) + y.2) =
      (μ.map (fun y => ∑ j, y j)) ∗ ν := by
    unfold Measure.conv
    rw [show (μ.map (fun y => ∑ j, y j)).prod ν =
        (μ.map (fun y => ∑ j, y j)).prod (ν.map id) by rw [Measure.map_id],
      Measure.map_prod_map _ _ (by fun_prop) measurable_id,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [hprod, old_sum_law P Λ u d σ target center hages lo hi]
  exact gaussian_split P Λ u d lo hi hdisjoint σ target center hages 0 θ

/-- Exact Fubini representation of every bounded Borel physical test on
the fixed old fractions and the actual varying residual Gaussian. -/
theorem average_split (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d : CircleL2)
    (lo hi : Fin r → ℝ) (hdisjoint : ∀ j k, j ≠ k → hi j ≤ lo k ∨ hi k ≤ lo j)
    (σ target : Fin n → ℝ) (center : Fin n → HeatCircle) (hages : ∀ i, σ i ≤ target i)
    (θ : ℝ) (F : State n → ℝ) (hF : Measurable F) (B : ℝ) (hb : ∀ z, |F z| ≤ B) (m : State n) :
    (∫ old, ∫ y, F (m + (∑ j, old j) + y)
      ∂multivariateGaussian (0 : State n) (ControlledFixedReserve.covariance P Λ u d
        (fixedProfile P Λ u d lo hi) σ target center 0 θ)
      ∂Measure.pi (fun j => multivariateGaussian (0 : State n)
        (familyCovariance σ target center (referenceProfile P Λ u d) lo hi j))) =
      GaussianConvolution.gaussianAverage
        (stoppedCovariance σ target center (fun p => profile P Λ u d (θ, p)) 0) F m := by
  let μ := Measure.pi (fun j => multivariateGaussian (0 : State n)
    (familyCovariance σ target center (referenceProfile P Λ u d) lo hi j))
  let ν := multivariateGaussian (0 : State n) (ControlledFixedReserve.covariance P Λ u d
    (fixedProfile P Λ u d lo hi) σ target center 0 θ)
  have hfi : Integrable (fun z : (Fin r → State n) × State n => F (m + (∑ j, z.1 j) + z.2)) (μ.prod ν) :=
    FiniteCenteredProduct.integrable_bounded _ _ (by fun_prop) B (fun _ => hb _)
  have hm := integral_map (μ := μ.prod ν) (φ := fun z : (Fin r → State n) × State n => (∑ j, z.1 j) + z.2)
    (f := fun z => F (m + z)) (by fun_prop)
    ((hF.comp (measurable_const.add measurable_id)).aestronglyMeasurable)
  rw [full_split_law P Λ u d lo hi hdisjoint σ target center hages θ] at hm
  calc
    _ = ∫ z : (Fin r → State n) × State n, F (m + (∑ j, z.1 j) + z.2) ∂μ.prod ν := by
      convert! (integral_prod _ hfi).symm using 1
    _ = _ := by simpa only [Function.comp_def, add_assoc, GaussianConvolution.gaussianAverage] using hm.symm

end SHE.ControlledOldIntervals
