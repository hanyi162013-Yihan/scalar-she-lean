module

public import SHE.GaussianIncrement
public import SHE.GaussianTaylor
public import SHE.GaussianConvolution

@[expose] public section
set_option autoImplicit false

/-! The actual second-order Gaussian covariance increment formula. -/
noncomputable section
namespace SHE.GaussianTaylorAverage
open Set MeasureTheory ProbabilityTheory Filter GaussianIncrement GaussianTaylor
open scoped MeasureTheory

def covarianceAction {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (H : State n →L[ℝ] State n →L[ℝ] ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, A i j * H (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)

theorem quadratic_integrable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (H : State n →L[ℝ] State n →L[ℝ] ℝ) :
    Integrable (fun x => H x x) (multivariateGaussian 0 A) := by
  have hi := (IsGaussian.memLp_id (multivariateGaussian (0 : State n) A) 2 (by norm_num)).integrable_norm_pow
    (p := 2) (by norm_num)
  apply (hi.const_mul ‖H‖).mono'
  · exact ((H.continuous.comp continuous_id).clm_apply continuous_id).aestronglyMeasurable
  · filter_upwards with x
    simpa only [id_eq, pow_two, mul_assoc] using bilinear_norm_le H x x

theorem gaussian_increment_quadratic_bound {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) {F : State n → ℝ} (hF : ContDiff ℝ 2 F)
    {M B : ℝ} (hbound : ∀ z, ‖F z‖ ≤ M) (hB : 0 ≤ B)
    (hDD : ∀ z, ‖hessian F z‖ ≤ B) (z : State n) :
    ‖GaussianConvolution.gaussianAverage A F z - F z‖ ≤ B * A.trace := by
  let μ := multivariateGaussian (0 : State n) A
  let R : State n → ℝ := fun x => F (z + x) - F z - fderiv ℝ F z x
  have hi2 := (IsGaussian.memLp_id μ 2 (by norm_num)).integrable_norm_pow (p := 2) (by norm_num)
  simp only [id_eq] at hi2
  have hrbound (x : State n) : ‖R x‖ ≤ B * ‖x‖ ^ 2 := first_order_remainder hF hB hDD z x
  have hFi := GaussianSmooth.integrable_translate μ hF.continuous hbound z
  have hLi : Integrable (fun x => fderiv ℝ F z x) μ :=
    (fderiv ℝ F z).integrable_comp IsGaussian.integrable_id
  have hLmean := (fderiv ℝ F z).integral_comp_comm (IsGaussian.integrable_id (μ := μ))
  simp only [id_eq, μ, integral_id_multivariateGaussian, map_zero] at hLmean
  have he : (∫ x, R x ∂μ) = GaussianConvolution.gaussianAverage A F z - F z := by
    have he1 := integral_sub hFi (integrable_const (F z))
    have he2 := integral_sub (hFi.sub (integrable_const (F z))) hLi
    simp only [Pi.sub_apply] at he1 he2
    dsimp only [R]
    rw [he2, he1, integral_const, hLmean]
    simp only [probReal_univ, one_smul, sub_zero, GaussianConvolution.gaussianAverage, μ]
  rw [← he]
  calc
    _ ≤ ∫ x, B * ‖x‖ ^ 2 ∂μ := norm_integral_le_of_norm_le (hi2.const_mul B)
      (Eventually.of_forall hrbound)
    _ = B * A.trace := by rw [integral_const_mul, norm_second_moment hA]

/-- A covariance increment is evaluated against every genuine mixed Hessian
entry. The error is controlled by the proved third Gaussian moment. -/
theorem gaussian_increment_taylor {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) {F : State n → ℝ} (hF : ContDiff ℝ 2 F)
    {M B : ℝ} (hbound : ∀ z, ‖F z‖ ≤ M) (hB : 0 ≤ B)
    (hH : ∀ z w, ‖hessian F w - hessian F z‖ ≤ B * ‖w - z‖) (z : State n) :
    ‖(∫ x, F (z + x) ∂multivariateGaussian 0 A) - F z -
      (1 / 2 : ℝ) * covarianceAction A (hessian F z)‖ ≤
      B * (Real.sqrt (3 * n) * A.trace * Real.sqrt A.trace) := by
  let μ := multivariateGaussian (0 : State n) A
  let R : State n → ℝ := fun x => F (z + x) - F z - fderiv ℝ F z x - (1 / 2 : ℝ) * hessian F z x x
  have hi3 := (IsGaussian.memLp_id μ 3 (by norm_num)).integrable_norm_pow (p := 3) (by norm_num)
  simp only [id_eq] at hi3
  have hrbound (x : State n) : ‖R x‖ ≤ B * ‖x‖ ^ 3 := second_order_remainder hF hB hH z x
  have hri : Integrable R μ := (hi3.const_mul B).mono' (by
      dsimp [R, hessian]
      exact ((((hF.continuous.comp (continuous_const.add continuous_id)).sub continuous_const).sub
        (fderiv ℝ F z).continuous).sub
          (continuous_const.mul (((fderiv ℝ (fderiv ℝ F) z).continuous.comp continuous_id).clm_apply continuous_id))).aestronglyMeasurable)
    (by filter_upwards with x; simpa only [id_eq] using hrbound x)
  have hFi := GaussianSmooth.integrable_translate μ hF.continuous hbound z
  have hLi : Integrable (fun x => fderiv ℝ F z x) μ :=
    (fderiv ℝ F z).integrable_comp IsGaussian.integrable_id
  have hLmean := (fderiv ℝ F z).integral_comp_comm (IsGaussian.integrable_id (μ := μ))
  simp only [id_eq, μ, integral_id_multivariateGaussian, map_zero] at hLmean
  have hQi := quadratic_integrable A (hessian F z)
  have he : (∫ x, R x ∂μ) = (∫ x, F (z + x) ∂μ) - F z -
      (1 / 2 : ℝ) * covarianceAction A (hessian F z) := by
    have he1 := integral_sub hFi (integrable_const (F z))
    have he2 := integral_sub (hFi.sub (integrable_const (F z))) hLi
    have he3 := integral_sub ((hFi.sub (integrable_const (F z))).sub hLi) (hQi.const_mul (1 / 2 : ℝ))
    simp only [Pi.sub_apply] at he1 he2 he3
    dsimp only [R]
    rw [he3, he2, he1, integral_const, integral_const_mul, hLmean]
    simp only [μ, probReal_univ, one_smul,
      sub_zero, quadratic_moment hA, covarianceAction]
  rw [← he]
  calc
    _ ≤ ∫ x, B * ‖x‖ ^ 3 ∂μ := norm_integral_le_of_norm_le (hi3.const_mul B) (by
      filter_upwards with x
      simpa only [id_eq] using hrbound x)
    _ = B * (∫ x, ‖x‖ ^ 3 ∂μ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (norm_third_moment_bound hA) hB

/-- A true covariance increment expansion about an arbitrary singular
Gaussian background. Both the Hessian and the covariance are the actual
Gaussian convolution objects, rather than supplied score identities. -/
theorem gaussian_covariance_increment {n : ℕ}
    {A C : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (hC : C.PosSemidef)
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L D K : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖hessian F z‖ ≤ D) (hK : 0 ≤ K)
    (hH : ∀ z w, ‖hessian F w - hessian F z‖ ≤ K * ‖w - z‖) (z : State n) :
    ‖GaussianConvolution.gaussianAverage (C + A) F z - GaussianConvolution.gaussianAverage C F z -
      (1 / 2 : ℝ) * covarianceAction A (hessian (GaussianConvolution.gaussianAverage C F) z)‖ ≤
      K * (Real.sqrt (3 * n) * A.trace * Real.sqrt A.trace) := by
  let μ := multivariateGaussian (0 : State n) C
  have hFavg := GaussianSmooth.contDiff_average_two μ hF hbound hD hDD
  have hboundavg := GaussianSmooth.average_norm_bound μ hbound
  have hHavg (v w : State n) := GaussianSmooth.average_hessian_lipschitz μ hF hbound hD hDD hH v w
  have he := gaussian_increment_taylor hA hFavg hboundavg hK hHavg z
  have heq : GaussianSmooth.average μ F = GaussianConvolution.gaussianAverage C F := rfl
  rw [heq] at he
  change ‖GaussianConvolution.gaussianAverage A (GaussianConvolution.gaussianAverage C F) z -
    GaussianConvolution.gaussianAverage C F z - (1 / 2 : ℝ) *
      covarianceAction A (hessian (GaussianConvolution.gaussianAverage C F) z)‖ ≤ _ at he
  rw [GaussianConvolution.gaussianAverage_composition A C hA hC F hF.continuous.measurable
    (by simpa only [Real.norm_eq_abs] using hbound) z, show A + C = C + A from add_comm A C] at he
  exact he

/-- The bounded Hessian controls a full PSD covariance increment linearly
in its trace, including a singular Gaussian background. -/
theorem gaussian_covariance_quadratic_bound {n : ℕ}
    {A C : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (hC : C.PosSemidef)
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L B : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖hessian F z‖ ≤ B) (hB : 0 ≤ B) (z : State n) :
    ‖GaussianConvolution.gaussianAverage (C + A) F z - GaussianConvolution.gaussianAverage C F z‖ ≤ B * A.trace := by
  let μ := multivariateGaussian (0 : State n) C
  have hFavg := GaussianSmooth.contDiff_average_two μ hF hbound hD hDD
  have hboundavg := GaussianSmooth.average_norm_bound μ hbound
  have hDDavg := GaussianSmooth.average_hessian_bound μ hF hbound hD hDD
  have he := gaussian_increment_quadratic_bound hA hFavg hboundavg hB hDDavg z
  have heq : GaussianSmooth.average μ F = GaussianConvolution.gaussianAverage C F := rfl
  rw [heq] at he
  rw [GaussianConvolution.gaussianAverage_composition A C hA hC F hF.continuous.measurable
    (by simpa only [Real.norm_eq_abs] using hbound) z, show A + C = C + A from add_comm A C] at he
  exact he

end SHE.GaussianTaylorAverage
