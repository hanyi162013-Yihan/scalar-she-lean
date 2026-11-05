module

public import SHE.GaussianWordCovarianceIntegral
public import SHE.GaussianVectorFractions

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace SHE.GaussianCoarseSecondScore
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution MeasurableGaussianScores
  GaussianWordCovarianceIntegral MeasurableGeneralizedInverse
open scoped InnerProductSpace
variable {n : ℕ}
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse

def constant (A : Matrix (Fin n) (Fin n) ℝ) : ℝ:=
  ‖(generalizedInverse A).toContinuousLinearMap‖^2*
    (∫ y : State n,‖y‖^2 ∂multivariateGaussian 0 A)+‖(generalizedInverse A).toContinuousLinearMap‖

theorem constant_nonneg (A : Matrix (Fin n) (Fin n) ℝ) : 0≤constant A:=
  add_nonneg (mul_nonneg (sq_nonneg _) (integral_nonneg (fun _=>sq_nonneg _))) (norm_nonneg _)

theorem secondScore_pointwise (A : Matrix (Fin n) (Fin n) ℝ) (d y : State n) :
    |secondScore A d y|≤‖d‖^2*
      (‖(generalizedInverse A).toContinuousLinearMap‖^2*‖y‖^2+‖(generalizedInverse A).toContinuousLinearMap‖) := by
  let K:=‖(generalizedInverse A).toContinuousLinearMap‖
  have hk : 0≤K:=norm_nonneg _
  have hd : ‖coefficient A d‖≤K*‖d‖:=by
    unfold coefficient
    change ‖(generalizedInverse A).toContinuousLinearMap d‖≤K*‖d‖
    exact (generalizedInverse A).toContinuousLinearMap.le_opNorm d
  have hf : |firstScore A d y|≤K*‖d‖*‖y‖:=by
    change |inner ℝ (coefficient A d) y|≤_
    exact (norm_inner_le_norm (𝕜:=ℝ) _ _).trans
      (mul_le_mul_of_nonneg_right hd (norm_nonneg _))
  have hsq:=pow_le_pow_left₀ (abs_nonneg (firstScore A d y)) hf 2
  rw [sq_abs] at hsq
  have hv:=GaussianWordCovarianceIntegral.scoreVariance_coarse_bound A d
  have hb:=abs_sub (firstScore A d y^2) (scoreVariance A d)
  rw [abs_sq] at hb
  change |secondScore A d y|≤_ at hb
  dsimp only [K] at *
  calc
    _ ≤ firstScore A d y^2+|scoreVariance A d| := hb
    _ ≤ (‖(generalizedInverse A).toContinuousLinearMap‖*‖d‖*‖y‖)^2+
        ‖(generalizedInverse A).toContinuousLinearMap‖*‖d‖^2 := add_le_add hsq hv
    _ = _ := by ring

theorem secondScore_l1 (A : Matrix (Fin n) (Fin n) ℝ) (d : State n) :
    (∫ y,|secondScore A d y| ∂multivariateGaussian 0 A)≤constant A*‖d‖^2 := by
  have hnorm : Integrable (fun y : State n=>‖y‖^2) (multivariateGaussian 0 A):=
    (IsGaussian.memLp_id (multivariateGaussian (0:State n) A) 2 (by norm_num)).integrable_norm_pow (by norm_num)
  have hi:=(GaussianVectorFractions.gaussian_secondScore_integrable A d).norm
  have hb:=integral_mono hi
    (((hnorm.const_mul (‖(generalizedInverse A).toContinuousLinearMap‖^2)).add (integrable_const _)).const_mul (‖d‖^2))
    (secondScore_pointwise A d)
  change (∫ y,|secondScore A d y| ∂multivariateGaussian 0 A)≤
    ∫ y,‖d‖^2*(‖(generalizedInverse A).toContinuousLinearMap‖^2*‖y‖^2+
      ‖(generalizedInverse A).toContinuousLinearMap‖) ∂multivariateGaussian 0 A at hb
  rw [integral_const_mul,integral_add
    (hnorm.const_mul (‖(generalizedInverse A).toContinuousLinearMap‖^2)) (integrable_const _),
    integral_const_mul,integral_const] at hb
  simpa only [constant,probReal_univ,one_smul,mul_comm] using hb

theorem rawMark_bound (A : Matrix (Fin n) (Fin n) ℝ) (F : State n→ℝ) (hF : Measurable F)
    (B : ℝ) (hB : ∀ y,|F y|≤B) (m d : State n) :
    |GaussianWordCovarianceIntegral.rawMark A F m d|≤B*constant A*‖d‖^2 := by
  have hB0 : 0≤B:=(abs_nonneg (F 0)).trans (hB 0)
  have hi : Integrable (fun y=>F (m+y)*secondScore A d y) (multivariateGaussian 0 A):=
    (GaussianVectorFractions.gaussian_secondScore_integrable A d).bdd_mul
      (hF.comp (measurable_const.add measurable_id)).aestronglyMeasurable
      (ae_of_all _ (fun y=>by simpa only [Real.norm_eq_abs] using hB (m+y)))
  calc
    _≤∫ y,|F (m+y)*secondScore A d y| ∂multivariateGaussian 0 A:=by
      simpa only [GaussianWordCovarianceIntegral.rawMark,Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun y : State n=>F (m+y)*secondScore A d y)
    _≤∫ y,B*|secondScore A d y| ∂multivariateGaussian 0 A:=by
      apply integral_mono hi.norm ((GaussianVectorFractions.gaussian_secondScore_integrable A d).norm.const_mul B)
      intro y
      change |F (m+y)*secondScore A d y|≤B*|secondScore A d y|
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hB _) (abs_nonneg _)
    _=B*(∫ y,|secondScore A d y| ∂multivariateGaussian 0 A):=integral_const_mul _ _
    _≤B*constant A*‖d‖^2:=by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (secondScore_l1 A d) hB0

theorem rawMark_outer_integrable {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (A : Matrix (Fin n) (Fin n) ℝ) (row : X→State n) (hr : Measurable row)
    (e : X→ℝ) (he : Measurable e) (henergy : Integrable (fun x=>|e x| * ‖row x‖^2) μ)
    (F : State n→ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ z,|F z|≤B) (m : State n) :
    Integrable (fun x=>e x*GaussianWordCovarianceIntegral.rawMark A F m (row x)) μ := by
  apply (henergy.const_mul (B*constant A)).mono'
    (he.mul ((rawMark_measurable A F hF m).comp hr)).aestronglyMeasurable
  filter_upwards with x
  change ‖e x*GaussianWordCovarianceIntegral.rawMark A F m (row x)‖≤_
  rw [Real.norm_eq_abs,abs_mul]
  convert! mul_le_mul_of_nonneg_left (rawMark_bound A F hF B hB m (row x)) (abs_nonneg (e x)) using 1
  ring
end SHE.GaussianCoarseSecondScore
