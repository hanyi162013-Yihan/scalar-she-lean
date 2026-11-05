module

public import SHE.GaussianMeanScores
public import SHE.GaussianConvolution

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.GaussianMeanScores
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution
  MeasurableGeneralizedInverse MeasurableGaussianScores
variable {n : ℕ}

theorem hasDerivAt_average_affine_zero {A : Mat n} (hA : A.PosSemidef) {D : State n}
    (hD : D ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) A).range)
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ y, |F y| ≤ M) (z : State n) :
    HasDerivAt (fun r : ℝ => gaussianAverage A F (z + r • D))
      (∫ y, F (z + y) * firstScore A D y ∂multivariateGaussian 0 A) 0 := by
  let Fz : State n → ℝ := fun y => F (z + y)
  have hh := hasDerivAt_physical_mean hA hD Fz
    (hF.comp (measurable_const.add measurable_id)) M (fun y => hM _) 0
  simp only [zero_smul, add_zero] at hh
  have he : (fun r : ℝ => gaussianAverage A F (z + r • D)) =
      fun r : ℝ => ∫ y, Fz (y + r • D) ∂multivariateGaussian 0 A := by
    funext r
    apply integral_congr_ae
    apply ae_of_all
    intro y
    change F (z + r • D + y) = F (z + (y + r • D))
    congr 1
    abel
  rw [← he] at hh
  exact hh

end SHE.GaussianMeanScores
