module

public import SHE.MovingMeanChain
public import SHE.GaussianSignedCovariance

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.GaussianMovingMean
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianTaylor GaussianTaylorAverage
  GaussianConvolution GaussianContinuity GaussianSignedCovariance
open scoped MatrixOrder Matrix.Norms.L2Operator Topology
variable {n : ℕ}

/-- Joint moving-mean differentiation from a proved covariance partial
derivative and continuous covariance. A uniform Taylor bound supplies the
missing diagonal chain rule. -/
theorem hasDerivAt_moving_mean_of_partial (C : ℝ → PositiveCovariance n) {θ a : ℝ}
    (hC : ContinuousAt C θ) (m : ℝ → State n) {d : State n} (hm : HasDerivAt m d θ)
    {F : State n → ℝ} (hc : HasDerivAt (fun s => gaussianAverage (C s).val F (m θ)) a θ)
    (hF : ContDiff ℝ 2 F) {M L B : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖hessian F z‖ ≤ B) (hB : 0 ≤ B) :
    HasDerivAt (fun s => gaussianAverage (C s).val F (m s))
      (a + fderiv ℝ (gaussianAverage (C θ).val F) (m θ) d) θ := by
  apply MovingMeanChain.hasDerivAt (G := fun s => fderiv ℝ (gaussianAverage (C s).val F) (m θ)) hc hm (B := B)
  · have hpc : ContinuousAt C θ := hC
    have hdf : Continuous (fderiv ℝ F) := (hF.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).continuous_fderiv (by norm_num)
    have hg := continuous_gaussian_average (fderiv ℝ F) hdf hD
    have he : (fun s => fderiv ℝ (gaussianAverage (C s).val F) (m θ)) =
        fun s => ∫ y, fderiv ℝ F (m θ + y) ∂multivariateGaussian 0 (C s).val := by
      funext s
      exact congrFun (GaussianSmooth.fderiv_average (multivariateGaussian 0 (C s).val)
        (hF.of_le (by norm_num)) hbound hD) (m θ)
    rw [he]
    have hp : ContinuousAt (fun s => (C s, m θ)) θ := hpc.prodMk continuousAt_const
    have hh := hg.continuousAt.comp hp
    exact hh
  · exact hB
  · intro s x
    have hs := GaussianSmooth.contDiff_average_two (multivariateGaussian 0 (C s).val) hF hbound hD hDD
    have hb := GaussianSmooth.average_hessian_bound (multivariateGaussian 0 (C s).val) hF hbound hD hDD
    exact GaussianTaylor.first_order_remainder hs hB hb (m θ) x


/-- The actual diagonal Gaussian curve has the sum of its covariance and
mean derivatives. A uniform Taylor remainder proves the joint chain rule. -/
theorem hasDerivAt_moving_mean (C : ℝ → PositiveCovariance n) {D : Mat n} {θ : ℝ}
    (hC : HasDerivAt (fun s => (C s).val) D θ)
    (m : ℝ → State n) {d : State n} (hm : HasDerivAt m d θ)
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L B K : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖hessian F z‖ ≤ B) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hH : ∀ z w, ‖hessian F w - hessian F z‖ ≤ K * ‖w - z‖) :
    HasDerivAt (fun s => gaussianAverage (C s).val F (m s))
      ((1 / 2 : ℝ) * covarianceAction D (hessian (gaussianAverage (C θ).val F) (m θ)) +
        fderiv ℝ (gaussianAverage (C θ).val F) (m θ) d) θ := by
  have hc := SHE.GaussianSignedCovariance.hasDerivAt_gaussian_average C hC hF hbound hD hDD hK hH (m θ)
  exact hasDerivAt_moving_mean_of_partial C (tendsto_subtype_rng.mpr hC.continuousAt) m hm
    hc hF hbound hD hDD hB

end SHE.GaussianMovingMean
