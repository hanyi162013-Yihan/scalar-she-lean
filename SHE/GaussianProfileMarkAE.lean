module

public import SHE.GaussianProfileMark
public import SHE.MeasuredRealCurves

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Continuum covariance marks at a.e. differentiability parameters. Only
pointwise differentiability at the chosen parameter is required; a genuine
integrable Lipschitz envelope justifies interchange with the covariance integral. -/
noncomputable section
namespace SHE.GaussianProfileMarkAE
open MeasureTheory Set Filter SHE.WordRecursion SHE.GaussianContinuity
  SHE.GaussianSignedCovariance SHE.GaussianTaylorAverage SHE.GaussianConvolution
  SHE.GaussianProfileMark
open scoped InnerProductSpace MatrixOrder Matrix.Norms.L2Operator NNReal Topology

/-- Differentiation of an actual continuum covariance at one parameter.
The scalar profile need not be differentiable at any other parameter. -/
theorem hasDerivAt_profileCovariance_of_lipschitz
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {n : ℕ}
    (c : ℝ → X → ℝ) (e : X → ℝ) (v : X → State n) {θ₀ : ℝ}
    (hv : AEStronglyMeasurable v μ)
    (hc : ∀ᶠ θ in nhds θ₀, AEStronglyMeasurable (c θ) μ)
    (hci : Integrable (fun x => |c θ₀ x| * ‖v x‖ ^ 2) μ)
    (he : AEStronglyMeasurable e μ) (g : X → ℝ)
    (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hgi : Integrable (fun x => g x * ‖v x‖ ^ 2) μ)
    (hlip : ∀ᵐ x ∂μ, LipschitzWith (Real.nnabs (g x)) (fun θ => c θ x))
    (hdiff : ∀ᵐ x ∂μ, HasDerivAt (fun θ => c θ x) (e x) θ₀) :
    Integrable (fun x => e x • rankMatrix (v x)) μ ∧
    HasDerivAt (fun θ => profileCovariance μ (c θ) v)
      (profileCovariance μ e v) θ₀ := by
  have hvr := (continuous_rankMatrix n).comp_aestronglyMeasurable hv
  apply hasDerivAt_integral_of_dominated_loc_of_lip
    (F := fun θ x => c θ x • rankMatrix (v x))
    (F' := fun x => e x • rankMatrix (v x))
    (bound := fun x => g x * ‖v x‖ ^ 2) (s := univ) Filter.univ_mem
    (hc.mono (fun θ hθ => hθ.smul hvr))
    (profileCovariance_integrable μ (c θ₀) v hc.self_of_nhds hv hci)
    (he.smul hvr) _ hgi
    (hdiff.mono (fun x hx => hx.smul_const (rankMatrix (v x))))
  filter_upwards [hlip, hg0] with x hx hg
  apply LipschitzWith.lipschitzOnWith
  apply LipschitzWith.of_dist_le_mul
  intro θ η
  have hs := hx.norm_sub_le θ η
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.coe_nnabs, abs_of_nonneg hg] at hs
  rw [dist_eq_norm, Real.coe_nnabs, Real.dist_eq]
  rw [← sub_smul, norm_smul, Real.norm_eq_abs, rankMatrix_norm,
    abs_of_nonneg (mul_nonneg hg (sq_nonneg _))]
  calc
    _ ≤ (g x * |θ - η|) * ‖v x‖ ^ 2 := mul_le_mul_of_nonneg_right hs (sq_nonneg _)
    _ = _ := by ring

/-- Actual nonmonotone Gaussian covariance differentiation with a signed
continuum profile mark, valid at any a.e. scalar differentiability parameter. -/
theorem hasDerivAt_profile_gaussian_average_of_lipschitz
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {n : ℕ}
    (c : ℝ → X → ℝ) (e : X → ℝ) (v : X → State n) {θ₀ : ℝ}
    (hv : AEStronglyMeasurable v μ)
    (hc : ∀ θ, AEStronglyMeasurable (c θ) μ)
    (hci : ∀ θ, Integrable (fun x => |c θ x| * ‖v x‖ ^ 2) μ)
    (hcpos : ∀ θ, ∀ᵐ x ∂μ, 0 ≤ c θ x)
    (he : AEStronglyMeasurable e μ) (g : X → ℝ)
    (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hgi : Integrable (fun x => g x * ‖v x‖ ^ 2) μ)
    (hlip : ∀ᵐ x ∂μ, LipschitzWith (Real.nnabs (g x)) (fun θ => c θ x))
    (hdiff : ∀ᵐ x ∂μ, HasDerivAt (fun θ => c θ x) (e x) θ₀)
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L B K : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖hessian F z‖ ≤ B) (hK : 0 ≤ K)
    (hH : ∀ z w, ‖hessian F w - hessian F z‖ ≤ K * ‖w - z‖) (z : State n) :
    HasDerivAt (fun θ => gaussianAverage (profileCovariance μ (c θ) v) F z)
      ((1 / 2 : ℝ) * ∫ x, e x *
        hessian (gaussianAverage (profileCovariance μ (c θ₀) v) F) z (v x) (v x) ∂μ) θ₀ := by
  have hi (θ : ℝ) := profileCovariance_integrable μ (c θ) v (hc θ) hv (hci θ)
  let C : ℝ → PositiveCovariance n := fun θ =>
    ⟨profileCovariance μ (c θ) v, profileCovariance_positive μ (c θ) v (hi θ) (hcpos θ)⟩
  obtain ⟨hei, hd⟩ := hasDerivAt_profileCovariance_of_lipschitz μ c e v hv
    (Eventually.of_forall hc) (hci θ₀) he g hg0 hgi hlip hdiff
  have hG := SHE.GaussianSignedCovariance.hasDerivAt_gaussian_average C hd
    hF hbound hD hDD hK hH z
  rw [profileCovariance_action μ e v hei] at hG
  exact hG

end SHE.GaussianProfileMarkAE
