module

public import SHE.GaussianMeanScores

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.GaussianMeanScores
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianAudit
  GaussianGramScore MeasurableGeneralizedInverse MeasurableGaussianScores
open scoped InnerProductSpace
variable {n : ℕ}

/-- The actual second physical mean derivative of every bounded Borel
test has its canonical centered-square score, including zero directions. -/
theorem hasDerivAt_deriv_physical_mean {A : Mat n} (hA : A.PosSemidef) {D : State n}
    (hD : D ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) A).range)
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ y, |F y| ≤ M) (θ : ℝ) :
    HasDerivAt (deriv (fun s : ℝ => ∫ y, F (y + s • D) ∂multivariateGaussian 0 A))
      (∫ y, F (y + θ • D) * secondScore A D y ∂multivariateGaussian 0 A) θ := by
  let μ := multivariateGaussian (0 : State n) A
  let L : State n →L[ℝ] ℝ := innerSL ℝ (coefficient A D)
  have hmean : (∫ y, L y ∂μ) = 0 := firstScore_mean_zero A D
  have hvar : Var[L; μ] = scoreVariance A D := firstScore_variance hA hD
  have hresp : covarianceResponse μ L = D := firstScore_response hA hD
  by_cases hV : 0 < scoreVariance A D
  · have hh := hasDerivAt_deriv_gaussian_covarianceResponse_mean μ L hmean
      (hvar.symm ▸ hV) F hF M hM θ
    rw [hresp, hvar] at hh
    exact hh
  · have hV0 : scoreVariance A D = 0 := le_antisymm (le_of_not_gt hV) (scoreVariance_nonneg hA hD)
    have hv0 : Var[L; μ] = 0 := hvar.trans hV0
    have hD0 : D = 0 := hresp.symm.trans (covarianceResponse_eq_zero_of_variance_eq_zero μ L hmean hv0)
    have hzero : L =ᵐ[μ] fun _ => 0 := by
      have hh := ae_eq_integral_of_variance_eq_zero (IsGaussian.memLp_dual μ L 2 (by norm_num)) hv0
      rw [hmean] at hh
      convert! hh using 1
    have hi : (∫ y, F (y + θ • D) * secondScore A D y ∂multivariateGaussian 0 A) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hzero] with y hy
      change F (y + θ • D) * (L y ^ 2 - scoreVariance A D) = 0
      rw [hy, hV0]
      ring
    rw [hi]
    have he : (fun s : ℝ => ∫ y, F (y + s • D) ∂multivariateGaussian 0 A) =
        fun _ => ∫ y, F y ∂μ := by
      funext s
      simp only [hD0, smul_zero, add_zero]
      rfl
    rw [he]
    simp only [deriv_const']
    exact hasDerivAt_const θ 0

end SHE.GaussianMeanScores
