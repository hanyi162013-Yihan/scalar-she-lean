module

public import SHEStochastic.IsotropicGaussianHolder
public import SHE.GaussianSmoothCovarianceBound

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.GaussianCovarianceHolder
open MeasureTheory ProbabilityTheory SHE SHE.GaussianIncrement SHE.GaussianAudit
  SHE.GaussianRangeSmooth SHE.GaussianTaylor SHE.GaussianConvolution SHE.GaussianSignedCovariance
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
variable {n : ℕ}

/-- A genuine covariance Lipschitz bound for bounded Hölder tests above
a positive isotropic floor. Both residual covariances may be singular,
and their difference need not have a sign. -/
theorem bound {r K β : ℝ} (hr : 0 < r) (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hb : ∀ y, |F y| ≤ M)
    (hh : ∀ x y, |F x-F y| ≤ K*‖x-y‖^β)
    (A C : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsotropicGaussianHolder.matrix r ≤ A) (hC : IsotropicGaussianHolder.matrix r ≤ C)
    (z : State n) :
    |gaussianAverage A F z-gaussianAverage C F z| ≤
      (K*secondScoreAbsIncrementMoment β*r^(β/2-1))*covarianceBoundConstant n*‖A-C‖ := by
  let R := IsotropicGaussianHolder.matrix (n := n) r
  have hR := IsotropicGaussianHolder.nonnegative (n := n) hr.le
  have hAR : (A-R).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hA)
  have hCR : (C-R).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hC)
  obtain ⟨hs, h0, h1, _, _, _⟩ := extension_covariance_regularity hR F hF hb
  have h2 := IsotropicGaussianHolder.hessian_norm_bound hr hK hβ F hF M hb hh
  have hB : 0 ≤ K*secondScoreAbsIncrementMoment β*r^(β/2-1) :=
    mul_nonneg (mul_nonneg hK (SHE.GaussianProfile.incrementMoment_nonneg β)) (Real.rpow_nonneg hr.le _)
  have hl := unordered_covariance_lipschitz hAR hCR hs h0 h1 h2 hB z
  have he (B : Matrix (Fin n) (Fin n) ℝ) (hB : (B-R).PosSemidef) :
      gaussianAverage (B-R) (roughAverageExtension R F) z = gaussianAverage B F z := by
    rw [reserve_average hR hB
      (by rw [IsotropicGaussianHolder.range_top hr.ne']; exact le_top) F hF M hb
      (by rw [IsotropicGaussianHolder.range_top hr.ne']; trivial)]
    congr 1
    abel
  rw [he A hAR, he C hCR, show A-R-(C-R) = A-C by abel] at hl
  exact hl

end SHEStochastic.GaussianCovarianceHolder
