module
public import SHE.GaussianHolderScore

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
namespace SHE.MatrixHolderScore
open MeasureTheory ProbabilityTheory GaussianIncrement GaussianAudit MeasurableGaussianScores
open scoped InnerProductSpace
variable {n:ℕ}

/-- The actual canonical second score gains the directional Hölder
modulus of its test. This includes zero and singular covariance cases. -/
theorem integral_bound {A:MeasurableGeneralizedInverse.Mat n} (hA:A.PosSemidef)
    {d:State n} (hd:d∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range)
    {F:State n→ℝ} (hF:Measurable F) {M K β:ℝ} (hb:∀x,|F x|≤M)
    (hK:0≤K) (hβ:0≤β)
    (hh:∀x s t,|F (x+s • d)-F (x+t • d)|≤K*|s-t|^β) (z:State n):
    |∫y,F (z+y)*MeasurableGaussianScores.secondScore A d y ∂multivariateGaussian 0 A|≤
      K*secondScoreAbsIncrementMoment β*scoreVariance A d^(1-β/2):=by
  let μ:=multivariateGaussian (0:State n) A
  let ℓ:State n→L[ℝ]ℝ:=innerSL ℝ (coefficient A d)
  let V:=scoreVariance A d
  have hmean:∫y,ℓ y ∂μ=0:=firstScore_mean_zero A d
  have hvar:Var[ℓ;μ]=V:=firstScore_variance hA hd
  have hresp:covarianceResponse μ ℓ=d:=firstScore_response hA hd
  have hV0:0≤V:=scoreVariance_nonneg hA hd
  by_cases hV:0<V
  · have hnormalized:normalizedCovarianceResponse μ ℓ=V⁻¹ • d:=by
      simp only [normalizedCovarianceResponse,hvar,hresp]
    have hmod:∀x s t,|F (x+s • normalizedCovarianceResponse μ ℓ)-
        F (x+t • normalizedCovarianceResponse μ ℓ)|≤(K*V^(-β))*|s-t|^β:=by
      intro x s t
      rw [hnormalized,smul_smul,smul_smul]
      have h:=hh x (s*V⁻¹) (t*V⁻¹)
      rw [show s*V⁻¹-t*V⁻¹=(s-t)*V⁻¹ by ring,abs_mul,abs_of_pos (inv_pos.mpr hV),
        Real.mul_rpow (abs_nonneg _) (inv_nonneg.mpr hV.le),Real.inv_rpow hV.le,
        ←Real.rpow_neg hV.le] at h
      convert h using 1 <;> ring
    have h:=GaussianHolderScore.centered_square_bound μ ℓ hmean (hvar.symm ▸ hV) hF hb
      (mul_nonneg hK (Real.rpow_nonneg hV.le _)) hβ hmod z
    rw [hvar] at h
    have hscore:∀y,MeasurableGaussianScores.secondScore A d y=(ℓ y)^2-V:=fun _=>rfl
    simp only [hscore]
    have hp:V^(-β)*V^(β/2+1)=V^(1-β/2):=by
      rw [←Real.rpow_add hV]
      congr 1
      ring
    have he:K*V^(-β)*secondScoreAbsIncrementMoment β*V^(β/2+1)=
        K*secondScoreAbsIncrementMoment β*V^(1-β/2):=by
      calc
        _=K*secondScoreAbsIncrementMoment β*(V^(-β)*V^(β/2+1)):=by ring
        _=_:=by rw [hp]
    exact h.trans_eq he
  · have hzero:Var[ℓ;μ]=0:=hvar.trans (le_antisymm (le_of_not_gt hV) hV0)
    have hz:ℓ=ᵐ[μ] fun _=>0:=by
      have h:=ae_eq_integral_of_variance_eq_zero (IsGaussian.memLp_dual μ ℓ 2 (by norm_num)) hzero
      rw [hmean] at h
      exact h
    have hi:(∫y,F (z+y)*MeasurableGaussianScores.secondScore A d y ∂μ)=0:=by
      apply integral_eq_zero_of_ae
      filter_upwards [hz] with y hy
      change F (z+y)*((ℓ y)^2-V)=0
      rw [hy,←hvar,hzero]
      simp only [zero_pow (by norm_num:2≠0),sub_zero,mul_zero]
    rw [hi,abs_zero]
    exact mul_nonneg (mul_nonneg hK (integral_nonneg (fun _=>by positivity))) (Real.rpow_nonneg hV0 _)

end SHE.MatrixHolderScore
