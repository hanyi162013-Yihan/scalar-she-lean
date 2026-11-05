module

public import SHE.GaussianProfileMarkAE

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.GaussianProfileMark
open Set MeasureTheory GaussianIncrement
open scoped MatrixOrder Matrix.Norms.L2Operator

theorem profileCovariance_norm_sub_le
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {n : ℕ}
    (c : ℝ → X → ℝ) (v : X → State n)
    (hv : AEStronglyMeasurable v μ) (hc : ∀ θ, AEStronglyMeasurable (c θ) μ)
    (hci : ∀ θ, Integrable (fun x => |c θ x| * ‖v x‖ ^ 2) μ)
    (g : X → ℝ) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hgi : Integrable (fun x => g x * ‖v x‖ ^ 2) μ)
    (hlip : ∀ᵐ x ∂μ, LipschitzWith (Real.nnabs (g x)) (fun θ => c θ x)) (θ η : ℝ) :
    ‖profileCovariance μ (c θ) v - profileCovariance μ (c η) v‖ ≤
      (∫ x, g x * ‖v x‖ ^ 2 ∂μ) * |θ - η| := by
  have hi (s : ℝ) := profileCovariance_integrable μ (c s) v (hc s) hv (hci s)
  change ‖(∫ x, c θ x • rankMatrix (v x) ∂μ) - ∫ x, c η x • rankMatrix (v x) ∂μ‖ ≤ _
  rw [← integral_sub (hi θ) (hi η)]
  have hh := norm_integral_le_of_norm_le (hgi.const_mul |θ - η|) (by
    filter_upwards [hg0, hlip] with x hg hx
    change ‖c θ x • rankMatrix (v x) - c η x • rankMatrix (v x)‖ ≤ |θ - η| * (g x * ‖v x‖ ^ 2)
    rw [← sub_smul, norm_smul, Real.norm_eq_abs, rankMatrix_norm]
    have hl := hx.norm_sub_le θ η
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.coe_nnabs, abs_of_nonneg hg] at hl
    have hi := mul_le_mul_of_nonneg_right hl (sq_nonneg ‖v x‖)
    convert! hi using 1 <;> ring)
  rw [integral_const_mul] at hh
  simpa only [mul_comm |θ - η|] using hh

theorem profileCovariance_lipschitz
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {n : ℕ}
    (c : ℝ → X → ℝ) (v : X → State n)
    (hv : AEStronglyMeasurable v μ) (hc : ∀ θ, AEStronglyMeasurable (c θ) μ)
    (hci : ∀ θ, Integrable (fun x => |c θ x| * ‖v x‖ ^ 2) μ)
    (g : X → ℝ) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hgi : Integrable (fun x => g x * ‖v x‖ ^ 2) μ)
    (hlip : ∀ᵐ x ∂μ, LipschitzWith (Real.nnabs (g x)) (fun θ => c θ x)) :
    LipschitzWith (Real.nnabs (∫ x, g x * ‖v x‖ ^ 2 ∂μ))
      (fun θ => profileCovariance μ (c θ) v) := by
  have hK : 0 ≤ ∫ x, g x * ‖v x‖ ^ 2 ∂μ :=
    integral_nonneg_of_ae (hg0.mono (fun x hx => mul_nonneg hx (sq_nonneg _)))
  apply LipschitzWith.of_dist_le_mul
  intro θ η
  rw [dist_eq_norm, Real.dist_eq, Real.coe_nnabs, abs_of_nonneg hK]
  exact profileCovariance_norm_sub_le μ c v hv hc hci g hg0 hgi hlip θ η

end SHE.GaussianProfileMark
