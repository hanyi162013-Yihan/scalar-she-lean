module

public import SHE.GaussianHolderScore
public import SHE.GaussianReserveAverage
public import SHEStochastic.SymmetricBilinearUnitBound
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.IsotropicGaussianHolder
open MeasureTheory ProbabilityTheory SHE SHE.GaussianIncrement SHE.GaussianAudit
  SHE.GaussianGramScore SHE.GaussianRangeSmooth SHE.GaussianTaylor
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
variable {n : ℕ}

def matrix (r : ℝ) : Matrix (Fin n) (Fin n) ℝ := r • 1

theorem nonnegative {r : ℝ} (hr : 0 ≤ r) : (matrix (n := n) r).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (show 0 ≤ r • (1 : Matrix (Fin n) (Fin n) ℝ) from smul_nonneg hr zero_le_one)

theorem action (r : ℝ) (u : State n) : Matrix.toEuclideanCLM (𝕜 := ℝ) (matrix r) u = r • u := by
  rw [matrix, map_smul, map_one]
  rfl

theorem range_top {r : ℝ} (hr : r ≠ 0) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (matrix (n := n) r)).range = ⊤ := by
  apply LinearMap.range_eq_top.mpr
  intro u
  refine ⟨r⁻¹ • u, ?_⟩
  change Matrix.toEuclideanCLM (𝕜 := ℝ) (matrix r) (r⁻¹ • u) = u
  rw [action, smul_smul, mul_inv_cancel₀ hr, one_smul]

theorem response {r : ℝ} (hr : 0 ≤ r) (d : State n) :
    covarianceResponse (multivariateGaussian 0 (matrix r)) (innerSL ℝ d) = r • d := by
  rw [gaussian_inner_covarianceResponse (nonnegative hr), action]

theorem variance {r : ℝ} (hr : 0 ≤ r) (d : State n) :
    Var[innerSL ℝ d; multivariateGaussian 0 (matrix r)] = r*‖d‖^2 := by
  rw [gaussian_inner_variance (nonnegative hr), action, inner_smul_right,
    real_inner_self_eq_norm_sq]

theorem unit_variance {r : ℝ} (hr : 0 ≤ r) (d : State n) (hd : ‖d‖ = 1) :
    Var[innerSL ℝ d; multivariateGaussian 0 (matrix r)] = r := by
  rw [variance hr, hd, one_pow, mul_one]

theorem normalized_response {r : ℝ} (hr : 0 < r) (d : State n) (hd : ‖d‖ = 1) :
    normalizedCovarianceResponse (multivariateGaussian 0 (matrix r)) (innerSL ℝ d) = d := by
  rw [normalizedCovarianceResponse, unit_variance hr.le d hd, response hr.le,
    smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

/-- The full-rank isotropic smoother has the centered-square score of
the original bounded Borel test. This reuses the proved native Gaussian
regression and the actual smooth range extension. -/
theorem hessian_score {r : ℝ} (hr : 0 < r) (F : State n → ℝ) (hF : Measurable F)
    (M : ℝ) (hb : ∀ y, |F y| ≤ M) (z d : State n) (hd : ‖d‖ = 1) :
    hessian (roughAverageExtension (matrix r) F) z (r • d) (r • d) =
      ∫ y, F (z+y)*((inner ℝ d y)^2-r) ∂multivariateGaussian 0 (matrix r) := by
  let R := matrix (n := n) r
  let μ := multivariateGaussian (0 : State n) R
  let f := roughAverageExtension R F
  obtain ⟨hs, h0, h1, h2, _, _⟩ := extension_covariance_regularity (nonnegative hr.le) F hF hb
  have hf : SHE.GaussianSmooth.average (Measure.dirac (0 : State n)) f = f := by
    funext x
    simp only [SHE.GaussianSmooth.average, integral_dirac, add_zero]
  have hline := SHE.GaussianHessianScore.hasDerivAt_deriv_average_affine_line
    (Measure.dirac (0 : State n)) hs h0 h1 h2 z (r • d)
  change HasDerivAt (deriv (fun s => SHE.GaussianSmooth.average (Measure.dirac (0 : State n)) f (z+s • (r • d))))
    (hessian (SHE.GaussianSmooth.average (Measure.dirac (0 : State n)) f) z (r • d) (r • d)) 0 at hline
  rw [hf] at hline
  let Fz : State n → ℝ := fun y => F (z+y)
  have hm : Measurable Fz := hF.comp (measurable_const.add measurable_id)
  have hmean : (∫ y, innerSL ℝ d y ∂μ) = 0 := gaussian_inner_mean_zero R d
  have hv : Var[innerSL ℝ d; μ] = r := unit_variance hr.le d hd
  have hresp : covarianceResponse μ (innerSL ℝ d) = r • d := response hr.le d
  have hraw := hasDerivAt_deriv_gaussian_covarianceResponse_mean μ (innerSL ℝ d) hmean
    (hv.symm ▸ hr) Fz hm M (fun y => hb _) 0
  have he : (fun s : ℝ => f (z+s • (r • d))) =
      (fun s => ∫ y, Fz (y+s • covarianceResponse μ (innerSL ℝ d)) ∂μ) := by
    funext s
    rw [show f (z+s • (r • d)) = SHE.GaussianConvolution.gaussianAverage R F (z+s • (r • d)) from
      extension_eq_average_on_range R F (by rw [range_top hr.ne']; trivial)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      rw [hresp]
      change F (z+s • (r • d)+y) = F (z+(y+s • (r • d)))
      congr 1
      abel
  rw [he] at hline
  have hh := hline.unique hraw
  simpa only [Fz, zero_smul, add_zero, hv, innerSL_apply_apply] using hh

theorem hessian_unit_bound {r K β : ℝ} (hr : 0 < r) (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hb : ∀ y, |F y| ≤ M)
    (hh : ∀ x y, |F x-F y| ≤ K*‖x-y‖^β) (z d : State n) (hd : ‖d‖ = 1) :
    |hessian (roughAverageExtension (matrix r) F) z d d| ≤
      K*secondScoreAbsIncrementMoment β*r^(β/2-1) := by
  let μ := multivariateGaussian (0 : State n) (matrix r)
  have hmean := gaussian_inner_mean_zero (matrix (n := n) r) d
  have hv : Var[innerSL ℝ d; μ] = r := unit_variance hr.le d hd
  have hdir (x : State n) (s t : ℝ) :
      |F (x+s • normalizedCovarianceResponse μ (innerSL ℝ d))-
        F (x+t • normalizedCovarianceResponse μ (innerSL ℝ d))| ≤ K*|s-t|^β := by
    rw [normalized_response hr d hd]
    have he : x+s • d-(x+t • d) = (s-t) • d := by module
    simpa only [he, norm_smul, Real.norm_eq_abs, hd, mul_one] using hh (x+s • d) (x+t • d)
  have hs := SHE.GaussianHolderScore.centered_square_bound μ (innerSL ℝ d) hmean
    (hv.symm ▸ hr) hF hb hK hβ hdir z
  rw [hv] at hs
  have he := hessian_score hr F hF M hb z d hd
  have hscale : hessian (roughAverageExtension (matrix r) F) z (r • d) (r • d) =
      r^2*hessian (roughAverageExtension (matrix r) F) z d d := by
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hb' : r^2*|hessian (roughAverageExtension (matrix r) F) z d d| ≤
      K*secondScoreAbsIncrementMoment β*r^(β/2+1) := by
    rw [hscale] at he
    change |∫ y, F (z+y)*((inner ℝ d y)^2-r) ∂multivariateGaussian 0 (matrix r)| ≤ _ at hs
    rw [← he, abs_mul, abs_of_nonneg (sq_nonneg _)] at hs
    exact hs
  apply le_of_mul_le_mul_left (a := r^2) ?_ (sq_pos_of_pos hr)
  apply hb'.trans_eq
  have hp : r^(β/2+1) = r^2*r^(β/2-1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hr]
    congr 1
    ring
  rw [hp]
  ring

/-- The actual full Gaussian Hessian gains the Hölder increment before
the score is estimated: its singularity is r^(beta/2-1). -/
theorem hessian_norm_bound {r K β : ℝ} (hr : 0 < r) (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hb : ∀ y, |F y| ≤ M)
    (hh : ∀ x y, |F x-F y| ≤ K*‖x-y‖^β) (z : State n) :
    ‖hessian (roughAverageExtension (matrix r) F) z‖ ≤
      K*secondScoreAbsIncrementMoment β*r^(β/2-1) := by
  have hs := contDiff_roughAverageExtension (nonnegative hr.le) F hF M hb 2
  apply SymmetricBilinearUnitBound.norm_le _ _
    (mul_nonneg (mul_nonneg hK (SHE.GaussianProfile.incrementMoment_nonneg β)) (Real.rpow_nonneg hr.le _))
  · exact hs.contDiffAt.isSymmSndFDerivAt (by norm_num)
  · exact hessian_unit_bound hr hK hβ F hF M hb hh z

end SHEStochastic.IsotropicGaussianHolder
