module

public import SHE.GaussianUniformFloor
public import SHE.ProfileCovarianceLipschitz

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.GaussianRangeSmooth
open Set MeasureTheory GaussianIncrement GaussianProfileMark GaussianContinuity
open scoped MatrixOrder Matrix.Norms.L2Operator NNReal

structure ProfileReserve {n : ℕ} (A : ℝ → Mat n) where
  floor : Mat n
  floor_positive : floor.PosSemidef
  residual : ℝ → PositiveCovariance n
  covariance_eq : ∀ θ, A θ = floor + (residual θ).val
  residual_range : ∀ θ, (Matrix.toEuclideanCLM (𝕜 := ℝ) (residual θ).val).range ≤
    (Matrix.toEuclideanCLM (𝕜 := ℝ) floor).range
  full_range : ∀ θ, (Matrix.toEuclideanCLM (𝕜 := ℝ) (A θ)).range =
    (Matrix.toEuclideanCLM (𝕜 := ℝ) floor).range

/-- Uniform scalar ellipticity constructs one actual positive Gaussian
reserve and a Lipschitz residual covariance path with exactly the same
physical range as every total covariance. -/
theorem exists_uniform_profile_reserve
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {n : ℕ}
    {ell : ℝ} (hell : 0 < ell) (c : ℝ → X → ℝ) (v : X → State n)
    (hv : AEStronglyMeasurable v μ) (henergy : Integrable (fun x => ‖v x‖ ^ 2) μ)
    (hc : ∀ θ, AEStronglyMeasurable (c θ) μ)
    (hci : ∀ θ, Integrable (fun x => |c θ x| * ‖v x‖ ^ 2) μ)
    (hclower : ∀ θ, ∀ᵐ x ∂μ, ell ≤ c θ x)
    (g : X → ℝ) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) (hgi : Integrable (fun x => g x * ‖v x‖ ^ 2) μ)
    (hlip : ∀ᵐ x ∂μ, LipschitzWith (Real.nnabs (g x)) (fun θ => c θ x)) :
    ∃ Q : ProfileReserve (fun θ => profileCovariance μ (c θ) v),
      ∃ K : ℝ≥0, LipschitzWith K (fun θ => (Q.residual θ).val) := by
  let α := ell / 2
  let r : ℝ → X → ℝ := fun θ x => c θ x - α
  let G := profileCovariance μ (fun _ => 1) v
  let R := α • G
  have hα : 0 < α := by dsimp [α]; positivity
  have hm (θ : ℝ) : AEStronglyMeasurable (r θ) μ := (hc θ).sub aestronglyMeasurable_const
  have hiw (θ : ℝ) : Integrable (fun x => |r θ x| * ‖v x‖ ^ 2) μ := by
    apply ((hci θ).add (henergy.const_mul |α|)).mono' ((hm θ).norm.mul (hv.norm.pow 2))
    filter_upwards with x
    change ‖|c θ x - α| * ‖v x‖ ^ 2‖ ≤ |c θ x| * ‖v x‖ ^ 2 + |α| * ‖v x‖ ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
    simpa only [add_mul] using mul_le_mul_of_nonneg_right (abs_sub (c θ x) α) (sq_nonneg ‖v x‖)
  have hp (θ : ℝ) : ∀ᵐ x ∂μ, 0 ≤ r θ x := by
    filter_upwards [hclower θ] with x hx
    dsimp [r, α]
    linarith
  have hl : ∀ᵐ x ∂μ, LipschitzWith (Real.nnabs (g x)) (fun θ => r θ x) := by
    filter_upwards [hlip] with x hx
    apply LipschitzWith.of_dist_le_mul
    intro θ η
    simpa only [r, dist_eq_norm, sub_sub_sub_cancel_right] using hx.dist_le_mul θ η
  have hiG : Integrable (fun x => (1 : ℝ) • rankMatrix (v x)) μ :=
    profileCovariance_integrable μ (fun _ => 1) v aestronglyMeasurable_const hv (by simpa using henergy)
  have hG : G.PosSemidef := profileCovariance_positive μ (fun _ => 1) v hiG (ae_of_all _ (by norm_num))
  have hR : R.PosSemidef := hG.smul hα.le
  have hr : (Matrix.toEuclideanCLM (𝕜 := ℝ) R).range = (Matrix.toEuclideanCLM (𝕜 := ℝ) G).range :=
    covariance_range_smul G hα.ne'
  have hvG := ae_frame_mem_gram_range μ v hv henergy
  have hvR : ∀ᵐ x ∂μ, v x ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) R).range := by simpa only [hr, G] using hvG
  have hi (θ : ℝ) := profileCovariance_integrable μ (r θ) v (hm θ) hv (hiw θ)
  have hpos (θ : ℝ) := profileCovariance_positive μ (r θ) v (hi θ) (hp θ)
  let C : ℝ → PositiveCovariance n := fun θ => ⟨profileCovariance μ (r θ) v, hpos θ⟩
  have hcov (θ : ℝ) : profileCovariance μ (c θ) v = R + (C θ).val := by
    have hh := profileCovariance_add_floor μ α (r θ) v (by simpa only [one_smul] using hiG) (hi θ)
    have heq : (fun x => α + r θ x) = c θ := by funext x; dsimp [r]; ring
    rw [heq] at hh
    exact hh
  have hres (θ : ℝ) : (Matrix.toEuclideanCLM (𝕜 := ℝ) (C θ).val).range ≤
      (Matrix.toEuclideanCLM (𝕜 := ℝ) R).range := profileCovariance_range_le μ (r θ) v (hi θ) _ hvR
  have hfull (θ : ℝ) : (Matrix.toEuclideanCLM (𝕜 := ℝ) (profileCovariance μ (c θ) v)).range =
      (Matrix.toEuclideanCLM (𝕜 := ℝ) R).range := by
    apply le_antisymm
    · exact profileCovariance_range_le μ (c θ) v
        (profileCovariance_integrable μ (c θ) v (hc θ) hv (hci θ)) _ hvR
    · rw [hcov]
      exact PositiveMatrixRanges.range_le_add_right hR (C θ).property
  refine ⟨⟨R, hR, C, hcov, hres, hfull⟩, Real.nnabs (∫ x, g x * ‖v x‖ ^ 2 ∂μ), ?_⟩
  exact profileCovariance_lipschitz μ r v hv hm hiw g hg0 hgi hl

end SHE.GaussianRangeSmooth
