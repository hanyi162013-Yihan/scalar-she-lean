module

public import SHE.GaussianRangeRegularity
public import SHE.GaussianRangeSupport
public import SHE.GaussianSignedCovariance

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-! A fixed physical Gaussian reserve turns bounded Borel covariance
averages into actual smooth-test averages on the residual covariance.
The equality uses actual Gaussian range support, including singular laws. -/
namespace SHE.GaussianRangeSmooth
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianTaylor GaussianTaylorAverage
  GaussianConvolution GaussianContinuity MeasurableGeneralizedInverse
open scoped InnerProductSpace
variable {n : ℕ}

theorem reserve_average {R B : Mat n} (hR : R.PosSemidef) (hB : B.PosSemidef)
    (hBR : (Matrix.toEuclideanCLM (𝕜 := ℝ) B).range ≤
      (Matrix.toEuclideanCLM (𝕜 := ℝ) R).range)
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ y, |F y| ≤ M)
    {z : State n} (hz : z ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) R).range) :
    gaussianAverage B (roughAverageExtension R F) z = gaussianAverage (R + B) F z := by
  calc
    _ = gaussianAverage B (gaussianAverage R F) z := by
      apply integral_congr_ae
      filter_upwards [ae_mem_covariance_range hB R hBR] with y hy
      change roughAverageExtension R F (z + y) = gaussianAverage R F (z + y)
      exact extension_eq_average_on_range R F (Submodule.add_mem _ hz hy)
    _ = gaussianAverage (B + R) F z := gaussianAverage_composition B R hB hR F hF hM z
    _ = _ := by rw [add_comm]

/-- Differentiation of the literal bounded-Borel Gaussian average along
any differentiable PSD residual path with a fixed physical range reserve.
Every smooth-test regularity premise is discharged by the construction. -/
theorem hasDerivAt_borel_reserve {R : Mat n} (hR : R.PosSemidef)
    (C : ℝ → PositiveCovariance n) {D : Mat n} {θ : ℝ}
    (hC : HasDerivAt (fun s => (C s).val) D θ)
    (hrange : ∀ s, (Matrix.toEuclideanCLM (𝕜 := ℝ) (C s).val).range ≤
      (Matrix.toEuclideanCLM (𝕜 := ℝ) R).range)
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ y, |F y| ≤ M)
    {z : State n} (hz : z ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) R).range) :
    HasDerivAt (fun s => gaussianAverage (R + (C s).val) F z)
      ((1 / 2 : ℝ) * covarianceAction D
        (hessian (gaussianAverage (C θ).val (roughAverageExtension R F)) z)) θ := by
  obtain ⟨hs, hb, hd, hdd, hk, hl⟩ := extension_covariance_regularity hR F hF hM
  have hh := SHE.GaussianSignedCovariance.hasDerivAt_gaussian_average C hC
    hs hb hd hdd hk hl z
  have he : (fun s => gaussianAverage (C s).val (roughAverageExtension R F) z) =
      fun s => gaussianAverage (R + (C s).val) F z :=
    funext (fun s => reserve_average hR (C s).property (hrange s) F hF M hM hz)
  rw [he] at hh
  exact hh

end SHE.GaussianRangeSmooth
