module

public import SHE.ControlledProfileParameter
public import SHE.StoppedProfileMark

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

/-! Actual signed profile marking for the prescribed damped controlled mean
and the full individually stopped covariance. This is the controlled profile
fixed point itself, rather than an identification with initial-data profiles. -/
namespace SHE.ControlledProfile
open Set MeasureTheory AddCircle StoppedFourier ProfileVariance
  StoppedGaussianFeatures StoppedProfileMark GaussianProfileMark GaussianProfileMarkAE
  GaussianContinuity GaussianConvolution GaussianTaylor ProfileParameter ProfilePointwise ProfileStability
open scoped MatrixOrder Matrix.Norms.L2Operator NNReal Topology
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable (P : CanonicalCovariance.ProfileParameters)

theorem ae_stopped_gaussian_mark {n : ℕ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hσ : ∀ i, 0 < σ i) (hσh : ∀ i, σ i ≤ P.horizon)
    (hages : ∀ i, σ i ≤ target i) (u d : CircleL2) {q : ℝ} (hq : 0 ≤ q)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent *
      ProfileVolterra.powerConstant ((P.exponent - 2) / 4) * P.horizon ^ (P.exponent / 4) ≤ 1 / 2)
    {F : WordRecursion.State n → ℝ} (hF : ContDiff ℝ 2 F) {M L B K : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖hessian F z‖ ≤ B) (hK : 0 ≤ K)
    (hH : ∀ z w, ‖hessian F w - hessian F z‖ ≤ K * ‖w - z‖) (z : WordRecursion.State n) :
    ∀ᵐ θ ∂volume,
      HasDerivAt (fun η => gaussianAverage
        (StoppedGaussianFeatures.stoppedCovariance σ target center (fun p => profile P Λ u d (η, p)) q) F z)
        ((1 / 2 : ℝ) * ∫ p : StoppedGaussianFeatures.Domain, derivative P Λ u d (p, θ) *
          hessian (gaussianAverage
            (StoppedGaussianFeatures.stoppedCovariance σ target center (fun p => profile P Λ u d (θ, p)) q) F) z
            (stoppedRow σ target center p) (stoppedRow σ target center p) ∂historyMeasure q) θ := by
  have hv := (stoppedRow_measurable σ target center).aestronglyMeasurable (μ := historyMeasure q)
  have hcm (θ : ℝ) : Measurable (fun p => profile P Λ u d (θ, p)) :=
    (profile_measurable P Λ u d).comp (measurable_const.prodMk measurable_id)
  have hc (θ : ℝ) := (hcm θ).aestronglyMeasurable (μ := historyMeasure q)
  have hcb (θ : ℝ) (p : Domain) : |profile P Λ u d (θ, p)| ≤ P.upper := by
    rw [abs_of_nonneg (P.lower_pos.le.trans (profile_bounds P Λ u d (θ, p)).1)]
    exact (profile_bounds P Λ u d (θ, p)).2
  have hci (θ : ℝ) := StoppedProfileMark.bounded_profile_frame_integrable σ target center hσ
    (fun i => (hσh i).trans P.horizon_le_one) hages hq (hcm θ) (hcb θ)
  have hcpos (θ : ℝ) : ∀ᵐ p ∂historyMeasure q, 0 ≤ profile P Λ u d (θ, p) :=
    ae_of_all _ (fun p => P.lower_pos.le.trans (profile_bounds P Λ u d (θ, p)).1)
  have he (θ : ℝ) : AEStronglyMeasurable (fun p => derivative P Λ u d (p, θ)) (historyMeasure q) :=
    ((derivative_measurable P hΛ u d hsmallPoint).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hlip : ∀ᵐ p ∂historyMeasure q,
      LipschitzWith (Real.nnabs (P.dominator d p)) (fun θ => profile P Λ u d (θ, p)) := by
    apply ae_of_all
    intro p
    apply LipschitzWith.of_dist_le_mul
    intro θ η
    have hh := (profile_curve_lipschitz P hΛ u d hsmallPoint p).dist_le_mul θ η
    rw [Real.coe_nnabs, abs_of_nonneg (P.dominator_nonneg d p)]
    exact hh
  have hd := ae_hasDerivAt P hΛ u d hsmallPoint (historyMeasure q)
  filter_upwards [hd] with θ hθ
  have hmark := hasDerivAt_profile_gaussian_average_of_lipschitz (historyMeasure q)
    (fun η p => profile P Λ u d (η, p)) (fun p => derivative P Λ u d (p, θ))
    (stoppedRow σ target center) hv hc hci hcpos (he θ) (P.dominator d)
    (ae_of_all _ (P.dominator_nonneg d))
    (P.stopped_dominator_frame_integrable σ target center hσ hσh hages d hq)
    hlip hθ hF hbound hD hDD hK hH z
  have heq (η : ℝ) := profileCovariance_eq_stopped σ target center hσ
    (fun i => (hσh i).trans P.horizon_le_one) hages hq (hcm η) (hcb η)
  simp_rw [heq] at hmark
  exact hmark

end SHE.ControlledProfile
