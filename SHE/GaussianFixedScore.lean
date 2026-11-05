module

public import SHE.GaussianHessianScore
public import SHE.GaussianRoughSecond
public import SHE.SmoothCylinderAlgebra

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.GaussianFixedScore
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution
  GaussianSmooth GaussianHessianScore SmoothCylinders MeasurableGaussianScores
variable {n : ℕ}

/-- A genuine Hessian of a bounded smooth test is represented by the
canonical score of the chosen fixed Gaussian fraction, at every mean.
Only the physical derivative direction must lie in its actual range. -/
theorem hessian_average_score {A : MeasurableGeneralizedInverse.Mat n} (hA : A.PosSemidef)
    {F : State n → ℝ} (hF : BoundedSmooth F) (z : State n) {d : State n}
    (hd : d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) A).range) :
    WordRecursion.directionalSecond (gaussianAverage A F) z d =
      ∫ y, F (z + y) * secondScore A d y ∂multivariateGaussian 0 A := by
  obtain ⟨M, hM⟩ := hF.norm_bound
  obtain ⟨L, hL⟩ := hF.fderiv.norm_bound
  obtain ⟨B, hB⟩ := hF.fderiv.fderiv.norm_bound
  let Fz : State n → ℝ := fun y => F (z + y)
  have hFz : Measurable Fz := hF.smooth.continuous.measurable.comp (measurable_const.add measurable_id)
  have hh := GaussianMeanScores.hasDerivAt_deriv_physical_mean hA hd Fz hFz M
    (fun y => by simpa only [Real.norm_eq_abs] using hM (z + y)) 0
  have hg := hasDerivAt_deriv_average_affine_line (multivariateGaussian (0 : State n) A)
    (hF.smooth.of_le (by simp)) hM hL hB z d
  have he : (fun s : ℝ => GaussianSmooth.average (multivariateGaussian (0 : State n) A) F (z + s • d)) =
      fun s : ℝ => ∫ y, Fz (y + s • d) ∂multivariateGaussian 0 A := by
    funext s
    apply integral_congr_ae
    apply ae_of_all
    intro y
    change F (z + s • d + y) = F (z + (y + s • d))
    congr 1
    abel
  rw [he] at hg
  simp only [zero_smul, add_zero] at hh
  exact hg.unique hh

/-- The old Gaussian fraction carries the Hessian score while the
remaining covariance stays inside the test.  The latter may be singular
and need not have its range inside the fixed old covariance. -/
theorem hessian_split_score {R B : MeasurableGeneralizedInverse.Mat n}
    (hR : R.PosSemidef) (hB : B.PosSemidef)
    {F : State n → ℝ} (hF : BoundedSmooth F) (z : State n) {d : State n}
    (hd : d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) R).range) :
    WordRecursion.directionalSecond (gaussianAverage (R + B) F) z d =
      ∫ old, ∫ residual, F (z + old + residual) * secondScore R d old
        ∂multivariateGaussian 0 B ∂multivariateGaussian 0 R := by
  obtain ⟨M, hM⟩ := hF.norm_bound
  have he : gaussianAverage (R + B) F = gaussianAverage R (gaussianAverage B F) := by
    funext w
    exact (gaussianAverage_composition R B hR hB F hF.smooth.continuous.measurable
      (fun w => by simpa only [Real.norm_eq_abs] using hM w) w).symm
  have hG : BoundedSmooth (gaussianAverage B F) :=
    hF.average (multivariateGaussian (0 : State n) B)
  rw [he, hessian_average_score hR hG z hd]
  apply integral_congr_ae
  apply ae_of_all
  intro old
  exact (integral_mul_const (secondScore R d old)
    (fun residual => F (z + old + residual))).symm

end SHE.GaussianFixedScore
