module

public import SHE.GaussianPositiveFloor

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.GaussianRangeSmooth
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianProfileMark
  GaussianConvolution MeasurableGaussianScores
open scoped InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

/-- Genuine bounded-Borel Gaussian profile differentiation. Uniform scalar
ellipticity supplies the reserve and every singular-range condition; the
mean is arbitrary. No regularity of the test beyond measurability remains. -/
theorem hasDerivAt_profile_borel_of_uniform_floor
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {n : ℕ}
    {ell : ℝ} (hell : 0 < ell) (c : ℝ → X → ℝ) (e : X → ℝ) (v : X → State n) {θ₀ : ℝ}
    (hv : AEStronglyMeasurable v μ) (henergy : Integrable (fun x => ‖v x‖ ^ 2) μ)
    (hc : ∀ θ, AEStronglyMeasurable (c θ) μ)
    (hci : ∀ θ, Integrable (fun x => |c θ x| * ‖v x‖ ^ 2) μ)
    (hclower : ∀ θ, ∀ᵐ x ∂μ, ell ≤ c θ x)
    (he : AEStronglyMeasurable e μ) (g : X → ℝ)
    (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) (hgi : Integrable (fun x => g x * ‖v x‖ ^ 2) μ)
    (hlip : ∀ᵐ x ∂μ, LipschitzWith (Real.nnabs (g x)) (fun θ => c θ x))
    (hdiff : ∀ᵐ x ∂μ, HasDerivAt (fun θ => c θ x) (e x) θ₀)
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ y, |F y| ≤ M) (z : State n) :
    HasDerivAt (fun θ => gaussianAverage (profileCovariance μ (c θ) v) F z)
      ((1 / 2 : ℝ) * ∫ x, e x *
        (∫ y, F (z + y) * secondScore (profileCovariance μ (c θ₀) v) (v x) y
          ∂multivariateGaussian 0 (profileCovariance μ (c θ₀) v)) ∂μ) θ₀ := by
  let α := ell / 2
  let r : ℝ → X → ℝ := fun θ x => c θ x - α
  have hα : 0 < α := by dsimp [α]; positivity
  have hm (θ : ℝ) : AEStronglyMeasurable (r θ) μ := (hc θ).sub aestronglyMeasurable_const
  have hi (θ : ℝ) : Integrable (fun x => |r θ x| * ‖v x‖ ^ 2) μ := by
    apply ((hci θ).add (henergy.const_mul |α|)).mono'
      ((hm θ).norm.mul (hv.norm.pow 2))
    filter_upwards with x
    change ‖|c θ x - α| * ‖v x‖ ^ 2‖ ≤ |c θ x| * ‖v x‖ ^ 2 + |α| * ‖v x‖ ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
    have hh := mul_le_mul_of_nonneg_right (abs_sub (c θ x) α) (sq_nonneg ‖v x‖)
    simpa only [add_mul] using hh
  have hp (θ : ℝ) : ∀ᵐ x ∂μ, 0 ≤ r θ x := by
    filter_upwards [hclower θ] with x hx
    dsimp [r, α]
    linarith
  have hl : ∀ᵐ x ∂μ, LipschitzWith (Real.nnabs (g x)) (fun θ => r θ x) := by
    filter_upwards [hlip] with x hx
    apply LipschitzWith.of_dist_le_mul
    intro θ η
    simpa only [r, dist_eq_norm, sub_sub_sub_cancel_right] using hx.dist_le_mul θ η
  have hd : ∀ᵐ x ∂μ, HasDerivAt (fun θ => r θ x) (e x) θ₀ :=
    hdiff.mono (fun x hx => hx.sub_const α)
  have hh := hasDerivAt_profile_borel_positive_floor μ hα r e v hv henergy hm hi hp he g
    hg0 hgi hl hd F hF M hM z
  have heq (θ : ℝ) : (fun x => α + r θ x) = c θ := by
    funext x
    dsimp [r]
    ring
  simp_rw [heq] at hh
  exact hh

end SHE.GaussianRangeSmooth
