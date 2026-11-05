module

public import SHE.GaussianTaylor

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.GaussianSmooth
open Set MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem mean_difference_bound (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E → ℝ} (hF : ContDiff ℝ 1 F) {M L : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L) (z w : E) :
    ‖average μ F z - average μ F w‖ ≤ L * ‖z - w‖ := by
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (s := Set.univ) (fun x _ => (hasFDerivAt_average μ hF hbound hD x).differentiableAt)
    (fun x _ => average_fderiv_bound μ hF hbound hD x) convex_univ (mem_univ w) (mem_univ z)

end SHE.GaussianSmooth
