module

public import SHEStochastic.IsotropicGaussianHolder
public import SHEStochastic.GaussianNormMoment
public import SHEStochastic.MatrixEllipticOperatorNorm

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.IsotropicGaussianMean
open MeasureTheory ProbabilityTheory SHE SHE.GaussianIncrement SHE.GaussianAudit
  SHE.GaussianGramScore SHE.GaussianRangeSmooth IsotropicGaussianHolder
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
variable {n : ℕ}

theorem gradient_score {r : ℝ} (hr : 0 < r) (F : State n → ℝ) (hF : Measurable F)
    (M : ℝ) (hb : ∀ y, |F y| ≤ M) (z d : State n) (hd : ‖d‖ = 1) :
    fderiv ℝ (roughAverageExtension (matrix r) F) z (r • d) =
      ∫ y, F (z+y)*inner ℝ d y ∂multivariateGaussian 0 (matrix r) := by
  let f := roughAverageExtension (matrix r) F
  have hs := contDiff_roughAverageExtension (nonnegative hr.le) F hF M hb 1
  have hp : HasDerivAt (fun s : ℝ => z+s • (r • d)) (r • d) 0 := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const (r • d)).const_add z
  have hl := (hs.differentiable (by norm_num) (z+(0 : ℝ) • (r • d))).hasFDerivAt.comp_hasDerivAt 0 hp
  let μ := multivariateGaussian (0 : State n) (matrix r)
  let Fz : State n → ℝ := fun y => F (z+y)
  have hm : Measurable Fz := hF.comp (measurable_const.add measurable_id)
  have hv : Var[innerSL ℝ d;μ] = r := unit_variance hr.le d hd
  have hraw := hasDerivAt_gaussian_covarianceResponse_mean μ (innerSL ℝ d)
    (gaussian_inner_mean_zero (matrix r) d) (hv.symm ▸ hr) Fz hm M (fun _ => hb _) 0
  have he : (fun s : ℝ => f (z+s • (r • d))) =
      (fun s => ∫ y, Fz (y+s • covarianceResponse μ (innerSL ℝ d)) ∂μ) := by
    funext s
    rw [show f (z+s • (r • d)) = GaussianConvolution.gaussianAverage (matrix r) F
        (z+s • (r • d)) from extension_eq_average_on_range _ _ (by rw [range_top hr.ne']; trivial)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      rw [response hr.le]
      change F (z+s • (r • d)+y) = F (z+(y+s • (r • d)))
      congr 1
      abel
  change HasDerivAt (fun s : ℝ => f (z+s • (r • d))) _ 0 at hl
  rw [he] at hl
  simpa only [Fz,zero_smul,add_zero,innerSL_apply_apply] using hl.unique hraw

theorem gradient_unit_bound {r K β : ℝ} (hr : 0 < r) (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hb : ∀ y, |F y| ≤ M)
    (hh : ∀ x y, |F x-F y| ≤ K*‖x-y‖^β) (z d : State n) (hd : ‖d‖ = 1) :
    |fderiv ℝ (roughAverageExtension (matrix r) F) z d| ≤
      K*GaussianNormMoment.moment (Fin n) (β+1)*r^((β-1)/2) := by
  let μ := multivariateGaussian (0 : State n) (matrix r)
  have hi := (IsGaussian.memLp_dual μ (innerSL ℝ d) 1 (by norm_num)).integrable (by norm_num)
  have hfi := hi.bdd_mul (hF.comp (measurable_const.add measurable_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by change ‖F (z+y)‖ ≤ M; exact hb (z+y))
  have hic := hi.const_mul (F z)
  change Integrable (fun y => F (z+y)*inner ℝ d y) μ at hfi
  change Integrable (fun y => F z*inner ℝ d y) μ at hic
  have he : (∫ y, F (z+y)*inner ℝ d y ∂μ) =
      ∫ y, (F (z+y)-F z)*inner ℝ d y ∂μ := by
    simp_rw [sub_mul]
    rw [integral_sub hfi hic,integral_const_mul]
    have hzero := gaussian_inner_mean_zero (matrix (n := n) r) d
    change (∫ y,inner ℝ d y ∂μ) = 0 at hzero
    rw [hzero,mul_zero,sub_zero]
  have hnorm : ∀ y : State n, ‖(F (z+y)-F z)*inner ℝ d y‖ ≤ K*‖y‖^(β+1) := by
    intro y
    rw [Real.norm_eq_abs,abs_mul,Real.rpow_add_one' (norm_nonneg y) (by linarith)]
    have hh' : |F (z+y)-F z| ≤ K*‖y‖^β := by simpa only [add_sub_cancel_left] using hh (z+y) z
    have hy : |inner ℝ d y| ≤ ‖y‖ := by simpa only [hd,one_mul] using abs_real_inner_le_norm d y
    exact (mul_le_mul hh' hy (abs_nonneg _) (mul_nonneg hK (Real.rpow_nonneg (norm_nonneg y) β))).trans_eq (by ring)
  have hm := GaussianNormMoment.bound (matrix (n := n) r) (nonnegative hr.le).nonneg hr.le
    (MatrixEllipticOperatorNorm.upper (matrix r) (nonnegative hr.le).nonneg r hr.le le_rfl)
    (by linarith : 0 ≤ β+1)
  have hbound : |∫ y, F (z+y)*inner ℝ d y ∂μ| ≤
      K*r^((β+1)/2)*GaussianNormMoment.moment (Fin n) (β+1) := by
    rw [he,← Real.norm_eq_abs]
    calc
      _ ≤ ∫ y : State n, K*‖y‖^(β+1) ∂μ :=
        norm_integral_le_of_norm_le ((GaussianNormMoment.integrable μ (by linarith : 0 ≤ β+1)).const_mul K)
          (Filter.Eventually.of_forall hnorm)
      _ ≤ _ := by rw [integral_const_mul]; exact (mul_le_mul_of_nonneg_left hm hK).trans_eq (by ring)
  rw [← gradient_score hr F hF M hb z d hd,map_smul,smul_eq_mul,abs_mul,abs_of_pos hr] at hbound
  apply le_of_mul_le_mul_left (a := r) ?_ hr
  apply hbound.trans_eq
  have hp : r*r^((β-1)/2) = r^((β+1)/2) := by
    calc
      _ = r^(1 : ℝ)*r^((β-1)/2) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hr]; congr 1; ring
  rw [show r*(K*GaussianNormMoment.moment (Fin n) (β+1)*r^((β-1)/2)) =
    K*(r*r^((β-1)/2))*GaussianNormMoment.moment (Fin n) (β+1) by ring,hp]

theorem gradient_norm_bound {r K β : ℝ} (hr : 0 < r) (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hb : ∀ y, |F y| ≤ M)
    (hh : ∀ x y, |F x-F y| ≤ K*‖x-y‖^β) (z : State n) :
    ‖fderiv ℝ (roughAverageExtension (matrix r) F) z‖ ≤
      K*GaussianNormMoment.moment (Fin n) (β+1)*r^((β-1)/2) := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm
    (mul_nonneg (mul_nonneg hK (GaussianNormMoment.nonneg _)) (Real.rpow_nonneg hr.le _))
  exact fun d hd => gradient_unit_bound hr hK hβ F hF M hb hh z d hd

end SHEStochastic.IsotropicGaussianMean
