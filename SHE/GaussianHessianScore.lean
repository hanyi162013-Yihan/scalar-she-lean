module

public import SHE.GaussianProfileMark

/-! Identification of the actual smoothed Hessian with the actual Gaussian
centered-square score, including covariance-range directions and singular
laws. This bridges continuum covariance marking to positive leverage. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.GaussianHessianScore
open MeasureTheory ProbabilityTheory Set Real SHE.GaussianAudit SHE.GaussianSmooth
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem hasDerivAt_deriv_average_affine_line (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {M L B : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ B) (z d : E) :
    HasDerivAt (deriv (fun s : ℝ => average μ F (z + s • d)))
      (fderiv ℝ (fderiv ℝ (average μ F)) z d d) 0 := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hpath (s : ℝ) : HasDerivAt (fun r : ℝ => z + r • d) d s := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id s).smul_const d).const_add z
  have hfirst (s : ℝ) := (hasFDerivAt_average μ hF1 hbound hD (z + s • d)).comp_hasDerivAt s (hpath s)
  have he : deriv (fun s : ℝ => average μ F (z + s • d)) =
      fun s => fderiv ℝ (average μ F) (z + s • d) d := by
    funext s
    simpa only [Function.comp_def, (hasFDerivAt_average μ hF1 hbound hD (z + s • d)).fderiv]
      using (hfirst s).deriv
  rw [he]
  have hbase := hasFDerivAt_fderiv_average μ hF hbound hD hDD z
  have hg := (hasFDerivAt_fderiv_average μ hF hbound hD hDD (z + (0 : ℝ) • d)).comp_hasDerivAt
    (0 : ℝ) (hpath 0)
  simp only [zero_smul, add_zero] at hg
  have hd := (ContinuousLinearMap.apply ℝ ℝ d).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hg
  rw [← hbase.fderiv] at hd
  convert! hd using 1

/-- The Gaussian Hessian in a covariance-range direction is literally the
centered-square score integral. This is derived by uniqueness of two
genuine second derivatives, not introduced as a Gaussian score axiom. -/
theorem hessian_average_covarianceResponse_score (μ : Measure E) [IsGaussian μ]
    (ℓ : E →L[ℝ] ℝ) (hMean : ∫ y, ℓ y ∂μ = 0) (hVar : 0 < Var[ℓ; μ])
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {M L B : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ B) (z : E) :
    fderiv ℝ (fderiv ℝ (average μ F)) z (covarianceResponse μ ℓ) (covarianceResponse μ ℓ) =
      ∫ y, F (z + y) * ((ℓ y) ^ 2 - Var[ℓ; μ]) ∂μ := by
  let d := covarianceResponse μ ℓ
  have hshift : Measurable (fun y : E => F (z + y)) :=
    hF.continuous.measurable.comp (measurable_const.add measurable_id)
  have hbshift (y : E) : |F (z + y)| ≤ M := by
    simpa only [Real.norm_eq_abs] using hbound (z + y)
  have hs := hasDerivAt_deriv_gaussian_covarianceResponse_mean μ ℓ hMean hVar
    (fun y => F (z + y)) hshift M hbshift 0
  have heq : (fun s : ℝ => ∫ y, F (z + (y + s • d)) ∂μ) =
      fun s : ℝ => average μ F (z + s • d) := by
    funext s
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => by
      change F (z + (y + s • d)) = F (z + s • d + y)
      congr 1
      abel)
  change HasDerivAt (deriv (fun s : ℝ => ∫ y, F (z + (y + s • d)) ∂μ)) _ 0 at hs
  rw [heq] at hs
  simp only [zero_smul, add_zero] at hs
  exact (hasDerivAt_deriv_average_affine_line μ hF hbound hD hDD z d).unique hs

omit [FiniteDimensional ℝ E] in
theorem centered_square_score_integral_bound (μ : Measure E) [IsGaussian μ]
    (ℓ : E →L[ℝ] ℝ) (hMean : ∫ y, ℓ y ∂μ = 0)
    (F : E → ℝ) (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ y, |F y| ≤ M) :
    |∫ y, F y * ((ℓ y) ^ 2 - Var[ℓ; μ]) ∂μ| ≤ 2 * M * Var[ℓ; μ] := by
  have hℓ := IsGaussian.memLp_dual μ ℓ 2 (by norm_num)
  have hsecond : (∫ y, (ℓ y) ^ 2 ∂μ) = Var[ℓ; μ] := by
    rw [variance_eq_integral hℓ.aemeasurable, hMean]
    simp only [sub_zero]
  have hi : Integrable (fun y => M * ((ℓ y) ^ 2 + Var[ℓ; μ])) μ :=
    (hℓ.integrable_sq.add (integrable_const _)).const_mul M
  have hp (y : E) : ‖F y * ((ℓ y) ^ 2 - Var[ℓ; μ])‖ ≤ M * ((ℓ y) ^ 2 + Var[ℓ; μ]) := by
    have hs : |(ℓ y) ^ 2 - Var[ℓ; μ]| ≤ (ℓ y) ^ 2 + Var[ℓ; μ] := by
      apply abs_le.mpr
      constructor <;> nlinarith [sq_nonneg (ℓ y), variance_nonneg ℓ μ]
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (hbound y) hs (abs_nonneg _) hM
  have hh := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hp)
  change |∫ y, F y * ((ℓ y) ^ 2 - Var[ℓ; μ]) ∂μ| ≤ _ at hh
  have he : (∫ y, M * ((ℓ y) ^ 2 + Var[ℓ; μ]) ∂μ) = 2 * M * Var[ℓ; μ] := by
    rw [integral_const_mul, integral_add hℓ.integrable_sq (integrable_const _), hsecond]
    simp only [integral_const, probReal_univ, one_smul]
    ring
  exact hh.trans_eq he

/-- The positive covariance-leverage bound for an actual smoothed Hessian.
The constant depends on the bounded test, not its spatial derivatives or
the conditioning of the full observation covariance. -/
theorem hessian_average_covarianceResponse_bound (μ : Measure E) [IsGaussian μ]
    (ℓ : E →L[ℝ] ℝ) (hMean : ∫ y, ℓ y ∂μ = 0)
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {M L B : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ B) (z : E) :
    |fderiv ℝ (fderiv ℝ (average μ F)) z
        (covarianceResponse μ ℓ) (covarianceResponse μ ℓ)| ≤ 2 * M * Var[ℓ; μ] := by
  have hM : 0 ≤ M := (norm_nonneg (F 0)).trans (hbound 0)
  by_cases hv : 0 < Var[ℓ; μ]
  · rw [hessian_average_covarianceResponse_score μ ℓ hMean hv hF hbound hD hDD]
    exact centered_square_score_integral_bound μ ℓ hMean (fun y => F (z + y)) M hM
      (fun y => by simpa only [Real.norm_eq_abs] using hbound (z + y))
  · have hv0 : Var[ℓ; μ] = 0 := le_antisymm (le_of_not_gt hv) (variance_nonneg ℓ μ)
    rw [covarianceResponse_eq_zero_of_variance_eq_zero μ ℓ hMean hv0, map_zero,
      abs_zero, hv0, mul_zero]

end SHE.GaussianHessianScore
