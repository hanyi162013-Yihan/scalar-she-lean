module

public import SHE.GaussianScoreKernel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

/-! Actual bounded rough-test mean differentiation along every physical
covariance-range direction, including zero-energy and singular cases. -/
namespace SHE.GaussianMeanScores
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianAudit
  GaussianGramScore MeasurableGeneralizedInverse MeasurableGaussianScores
open scoped InnerProductSpace
variable {n:ℕ}

theorem hasDerivAt_physical_mean {A:Mat n} (hA:A.PosSemidef) {D:State n}
    (hD:D∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range)
    (F:State n→ℝ) (hF:Measurable F) (M:ℝ) (hM:∀y,|F y|≤M) (θ:ℝ) :
    HasDerivAt (fun s:ℝ=>∫y,F (y+s•D) ∂multivariateGaussian 0 A)
      (∫y,F (y+θ•D)*firstScore A D y ∂multivariateGaussian 0 A) θ := by
  let μ:=multivariateGaussian (0:State n) A
  let L:State n→L[ℝ] ℝ:=innerSL ℝ (coefficient A D)
  have hmean:(∫y,L y ∂μ)=0:=firstScore_mean_zero A D
  have hvar:Var[L;μ]=scoreVariance A D:=firstScore_variance hA hD
  have hresp:covarianceResponse μ L=D:=firstScore_response hA hD
  by_cases hV:0<scoreVariance A D
  · have h:=hasDerivAt_gaussian_covarianceResponse_mean μ L hmean (hvar.symm ▸ hV) F hF M hM θ
    rw[hresp] at h
    exact h
  · have hV0:scoreVariance A D=0:=le_antisymm (le_of_not_gt hV) (scoreVariance_nonneg hA hD)
    have hvar0:Var[L;μ]=0:=hvar.trans hV0
    have hD0:D=0:=hresp.symm.trans (covarianceResponse_eq_zero_of_variance_eq_zero μ L hmean hvar0)
    have hzero:L=ᵐ[μ] fun _=>0:=by
      have h:=ae_eq_integral_of_variance_eq_zero (IsGaussian.memLp_dual μ L 2 (by norm_num)) hvar0
      rw [hmean] at h
      convert! h using 1
    have hi:(∫y,F (y+θ•D)*firstScore A D y ∂μ)=0:=by
      apply integral_eq_zero_of_ae
      filter_upwards[hzero] with y hy
      change F (y+θ•D)*L y=0
      rw[hy,mul_zero]
    have heq : (fun s:ℝ=>∫y,F (y+s•D) ∂multivariateGaussian 0 A) = fun _=>∫y,F y ∂μ := by
      funext s
      simp only [hD0,smul_zero,add_zero]
      rfl
    rw [heq]
    change HasDerivAt (fun _ : ℝ => ∫ y,F y ∂μ) (∫y,F (y+θ•D)*firstScore A D y ∂μ) θ
    rw [hi]
    exact hasDerivAt_const θ _

end SHE.GaussianMeanScores
