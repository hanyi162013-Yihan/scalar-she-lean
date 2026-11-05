module

public import SHE.GaussianReserveScore
public import SHE.GaussianProfileMarkAE

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-! Signed continuum covariance differentiation for bounded Borel tests,
using an actual fixed Gaussian reserve on the physical covariance range.
Only genuine covariance/profile applicability conditions remain. -/
namespace SHE.GaussianRangeSmooth
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianTaylor
  GaussianConvolution GaussianContinuity GaussianProfileMark GaussianProfileMarkAE
  MeasurableGaussianScores
open scoped InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

theorem hasDerivAt_profile_borel_reserve
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {n : ℕ}
    {R : Mat n} (hR : R.PosSemidef) (c : ℝ → X → ℝ) (e : X → ℝ) (v : X → State n) {θ₀ : ℝ}
    (hv : AEStronglyMeasurable v μ)
    (hc : ∀ θ, AEStronglyMeasurable (c θ) μ)
    (hci : ∀ θ, Integrable (fun x => |c θ x| * ‖v x‖ ^ 2) μ)
    (hcpos : ∀ θ, ∀ᵐ x ∂μ, 0 ≤ c θ x)
    (he : AEStronglyMeasurable e μ) (g : X → ℝ)
    (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) (hgi : Integrable (fun x => g x * ‖v x‖ ^ 2) μ)
    (hlip : ∀ᵐ x ∂μ, LipschitzWith (Real.nnabs (g x)) (fun θ => c θ x))
    (hdiff : ∀ᵐ x ∂μ, HasDerivAt (fun θ => c θ x) (e x) θ₀)
    (hrange : ∀ θ, (Matrix.toEuclideanCLM (𝕜 := ℝ) (profileCovariance μ (c θ) v)).range ≤
      (Matrix.toEuclideanCLM (𝕜 := ℝ) R).range)
    (hvR : ∀ᵐ x ∂μ, v x ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) R).range)
    (hvA : ∀ᵐ x ∂μ, v x ∈
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (R + profileCovariance μ (c θ₀) v)).range)
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ y, |F y| ≤ M)
    {z : State n} (hz : z ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) R).range) :
    HasDerivAt (fun θ => gaussianAverage (R + profileCovariance μ (c θ) v) F z)
      ((1 / 2 : ℝ) * ∫ x, e x *
        (∫ y, F (z + y) * secondScore (R + profileCovariance μ (c θ₀) v) (v x) y
          ∂multivariateGaussian 0 (R + profileCovariance μ (c θ₀) v)) ∂μ) θ₀ := by
  have hi (θ : ℝ) := profileCovariance_integrable μ (c θ) v (hc θ) hv (hci θ)
  have hp (θ : ℝ) := profileCovariance_positive μ (c θ) v (hi θ) (hcpos θ)
  obtain ⟨hs, hb, hd, hdd, hk, hH⟩ := extension_covariance_regularity hR F hF hM
  have hh := hasDerivAt_profile_gaussian_average_of_lipschitz μ c e v hv hc hci hcpos
    he g hg0 hgi hlip hdiff hs hb hd hdd hk hH z
  have hfun : (fun θ => gaussianAverage (profileCovariance μ (c θ) v) (roughAverageExtension R F) z) =
      fun θ => gaussianAverage (R + profileCovariance μ (c θ) v) F z :=
    funext (fun θ => reserve_average hR (hp θ) (hrange θ) F hF M hM hz)
  rw [hfun] at hh
  convert! hh using 1
  congr 1
  apply integral_congr_ae
  filter_upwards [hvR, hvA] with x hxR hxA
  apply congrArg (fun r : ℝ => e x * r)
  exact (reserve_hessian_score hR (hp θ₀) (hrange θ₀) F hF M hM hz hxR hxA).symm

end SHE.GaussianRangeSmooth
