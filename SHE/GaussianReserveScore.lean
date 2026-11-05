module

public import SHE.GaussianReserveAverage
public import SHE.GaussianRoughSecond

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.GaussianRangeSmooth
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianTaylor GaussianHessianScore
  GaussianConvolution GaussianContinuity MeasurableGeneralizedInverse MeasurableGaussianScores
open scoped InnerProductSpace
variable {n : ℕ}

/-- The residual smooth Hessian is exactly the actual total-covariance
canonical score for every bounded Borel test. Singular ranks are allowed. -/
theorem reserve_hessian_score {R B : Mat n} (hR : R.PosSemidef) (hB : B.PosSemidef)
    (hBR : (Matrix.toEuclideanCLM (𝕜 := ℝ) B).range ≤
      (Matrix.toEuclideanCLM (𝕜 := ℝ) R).range)
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ y, |F y| ≤ M)
    {z d : State n} (hz : z ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) R).range)
    (hdR : d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) R).range)
    (hdA : d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (R + B)).range) :
    hessian (gaussianAverage B (roughAverageExtension R F)) z d d =
      ∫ y, F (z + y) * secondScore (R + B) d y ∂multivariateGaussian 0 (R + B) := by
  obtain ⟨hs, hb, hd, hdd, _, _⟩ := extension_covariance_regularity hR F hF hM
  have hg := hasDerivAt_deriv_average_affine_line (multivariateGaussian 0 B)
    hs hb hd hdd z d
  change HasDerivAt (deriv (fun s : ℝ => gaussianAverage B (roughAverageExtension R F) (z + s • d)))
    (hessian (gaussianAverage B (roughAverageExtension R F)) z d d) 0 at hg
  let Fz : State n → ℝ := fun y => F (z + y)
  have he : (fun s : ℝ => gaussianAverage B (roughAverageExtension R F) (z + s • d)) =
      fun s : ℝ => ∫ y, Fz (y + s • d) ∂multivariateGaussian 0 (R + B) := by
    funext s
    rw [reserve_average hR hB hBR F hF M hM (Submodule.add_mem _ hz (Submodule.smul_mem _ s hdR))]
    apply integral_congr_ae
    apply ae_of_all
    intro y
    change F (z + s • d + y) = F (z + (y + s • d))
    congr 1
    abel
  rw [he] at hg
  have hh := GaussianMeanScores.hasDerivAt_deriv_physical_mean (hR.add hB) hdA Fz
    (hF.comp (measurable_const.add measurable_id)) M (fun y => hM _) 0
  simp only [zero_smul, add_zero] at hh
  exact hg.unique hh

end SHE.GaussianRangeSmooth
