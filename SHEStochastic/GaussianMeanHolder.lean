module

public import SHEStochastic.IsotropicGaussianMean
public import SHE.GaussianSmoothMeanBound
public import SHE.GaussianReserveAverage

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.GaussianMeanHolder
open MeasureTheory ProbabilityTheory SHE SHE.GaussianIncrement SHE.GaussianAudit
  SHE.GaussianRangeSmooth SHE.GaussianConvolution
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Full matrix ellipticity gives the same first-derivative Hölder gain
as in the scalar mean estimate. The remaining covariance may be singular. -/
theorem bound {r K β : ℝ} (hr : 0 < r) (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hb : ∀ y, |F y| ≤ M)
    (hh : ∀ x y, |F x-F y| ≤ K*‖x-y‖^β)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsotropicGaussianHolder.matrix r ≤ A)
    (z w : State n) :
    |gaussianAverage A F z-gaussianAverage A F w| ≤
      (K*GaussianNormMoment.moment (Fin n) (β+1)*r^((β-1)/2))*‖z-w‖ := by
  let R := IsotropicGaussianHolder.matrix (n := n) r
  have hR := IsotropicGaussianHolder.nonnegative (n := n) hr.le
  have hAR : (A-R).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hA)
  obtain ⟨hs,h0,_,_,_,_⟩ := extension_covariance_regularity hR F hF hb
  have hD := IsotropicGaussianMean.gradient_norm_bound hr hK hβ F hF M hb hh
  have hl := GaussianSmooth.mean_difference_bound (multivariateGaussian (0 : State n) (A-R))
    (hs.of_le (by norm_num)) h0 hD z w
  have he (v : State n) : GaussianSmooth.average (multivariateGaussian (0 : State n) (A-R))
      (roughAverageExtension R F) v = gaussianAverage A F v := by
    change gaussianAverage (A-R) (roughAverageExtension R F) v = _
    rw [reserve_average hR hAR (by rw [IsotropicGaussianHolder.range_top hr.ne']; exact le_top)
      F hF M hb (by rw [IsotropicGaussianHolder.range_top hr.ne']; trivial)]
    congr 1
    abel
  change ‖GaussianSmooth.average (multivariateGaussian (0 : State n) (A-R))
    (roughAverageExtension R F) z-GaussianSmooth.average (multivariateGaussian (0 : State n) (A-R))
    (roughAverageExtension R F) w‖ ≤ _ at hl
  rw [he z,he w,Real.norm_eq_abs] at hl
  exact hl

end SHEStochastic.GaussianMeanHolder
