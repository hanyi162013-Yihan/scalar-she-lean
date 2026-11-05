module

public import SHE.ProfileReserveAffine
public import SHE.GaussianMeanLine

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.GaussianRangeSmooth.ProfileReserve
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution
  MeasurableGaussianScores
open scoped NNReal Matrix.Norms.L2Operator
variable {n : ℕ} {A : ℝ → Matrix (Fin n) (Fin n) ℝ}

/-- The physical first-score contribution for an affine mean. -/
def affineMeanMark (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (F : State n → ℝ)
    (base d : State n) (θ : ℝ) : ℝ :=
  ∫ y, F (base + θ • d + y) * firstScore (A θ) d y ∂multivariateGaussian 0 (A θ)

/-- A common a.e. covariance-marking event may be evaluated at the moving
mean. The actual first-score mean contribution then gives the total derivative. -/
theorem ae_hasDerivAt_affine_total (Q : ProfileReserve A) {K : ℝ≥0}
    (hK : LipschitzWith K (fun θ => (Q.residual θ).val))
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ y, |F y| ≤ M)
    (base d : State n) (hd : d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (A 0)).range)
    (covMark : ℝ → State n → ℝ)
    (hcov : ∀ᵐ θ ∂volume, ∀ z, HasDerivAt (fun s => gaussianAverage (A s) F z) (covMark θ z) θ) :
    ∀ᵐ θ ∂volume, HasDerivAt (fun s => gaussianAverage (A s) F (base + s • d))
      (covMark θ (base + θ • d) + affineMeanMark A F base d θ) θ := by
  have hdr : d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) Q.floor).range := by
    simpa only [Q.full_range 0] using hd
  filter_upwards [hcov] with θ hθ
  have hdθ : d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (A θ)).range := by
    simpa only [Q.full_range θ] using hdr
  have hAθ : (A θ).PosSemidef := by
    rw [Q.covariance_eq θ]
    exact Q.floor_positive.add (Q.residual θ).property
  have hm := GaussianMeanScores.hasDerivAt_average_affine_zero hAθ hdθ F hF M hM (base + θ • d)
  exact Q.hasDerivAt_affine_of_partials hK F hF M hM base d hdθ (hθ _) hm

/-- The literal endpoint identity, including both covariance and mean marks,
for bounded Borel tests. Integrability follows from the proved Lipschitz curve. -/
theorem integral_affine_total (Q : ProfileReserve A) {K : ℝ≥0}
    (hK : LipschitzWith K (fun θ => (Q.residual θ).val))
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ y, |F y| ≤ M)
    (base d : State n) (hd : d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (A 0)).range)
    (covMark : ℝ → State n → ℝ)
    (hcov : ∀ᵐ θ ∂volume, ∀ z, HasDerivAt (fun s => gaussianAverage (A s) F z) (covMark θ z) θ)
    (a b : ℝ) :
    IntervalIntegrable (fun θ => covMark θ (base + θ • d) + affineMeanMark A F base d θ) volume a b ∧
      (∫ θ in a..b, covMark θ (base + θ • d) + affineMeanMark A F base d θ) =
        gaussianAverage (A b) F (base + b • d) - gaussianAverage (A a) F (base + a • d) := by
  exact Q.integral_affine hK F hF M hM base d hd _
    (Q.ae_hasDerivAt_affine_total hK F hF M hM base d hd covMark hcov) a b

end SHE.GaussianRangeSmooth.ProfileReserve
