module

public import SHE.ProfileReserveCalculus
public import SHE.GaussianSmoothMeanBound

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.GaussianRangeSmooth.ProfileReserve
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution GaussianSignedCovariance
open scoped NNReal Matrix.Norms.L2Operator
variable {n : ℕ} {A : ℝ → Matrix (Fin n) (Fin n) ℝ}

theorem exists_lipschitz_affine (Q : ProfileReserve A) {K : ℝ≥0}
    (hK : LipschitzWith K (fun θ => (Q.residual θ).val))
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ y, |F y| ≤ M)
    (base d : State n) (hd : d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (A 0)).range) :
    ∃ L : ℝ≥0, LipschitzWith L (fun θ => gaussianAverage (A θ) F (base + θ • d)) := by
  have hdr : d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) Q.floor).range := by simpa only [Q.full_range 0] using hd
  let F₀ : State n → ℝ := fun y => F (base + y)
  let H := roughAverageExtension Q.floor F₀
  have hm : Measurable F₀ := hF.comp (measurable_const.add measurable_id)
  have hb : ∀ y, |F₀ y| ≤ M := fun y => hM _
  obtain ⟨hs, h0, h1, h2, _, _⟩ := extension_covariance_regularity Q.floor_positive F₀ hm hb
  have hM0 : 0 ≤ M := (abs_nonneg (F 0)).trans (hM 0)
  let L₁ := M * extensionJetConstant Q.floor 1
  let B := M * extensionJetConstant Q.floor 2
  let T := B * covarianceBoundConstant n * (K : ℝ) + L₁ * ‖d‖
  have hL₁ : 0 ≤ L₁ := mul_nonneg hM0 (extensionJetConstant_nonneg Q.floor 1)
  have hB : 0 ≤ B := mul_nonneg hM0 (extensionJetConstant_nonneg Q.floor 2)
  have hBC : 0 ≤ B * covarianceBoundConstant n := mul_nonneg hB (covarianceBoundConstant_nonneg n)
  have hT : 0 ≤ T := add_nonneg (mul_nonneg hBC K.coe_nonneg) (mul_nonneg hL₁ (norm_nonneg _))
  have he (s : ℝ) : gaussianAverage (Q.residual s).val H (s • d) = gaussianAverage (A s) F (base + s • d) := by
    have hh := reserve_average Q.floor_positive (Q.residual s).property (Q.residual_range s)
      F₀ hm M hb (Submodule.smul_mem _ s hdr)
    rw [← Q.covariance_eq s] at hh
    rw [hh]
    apply integral_congr_ae
    apply ae_of_all
    intro y
    change F (base + (s • d + y)) = F (base + s • d + y)
    rw [add_assoc]
  refine ⟨Real.nnabs T, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro θ η
  rw [dist_eq_norm, Real.dist_eq, Real.coe_nnabs, abs_of_nonneg hT, ← he θ, ← he η]
  have hc := unordered_covariance_lipschitz (Q.residual θ).property (Q.residual η).property
    hs h0 h1 h2 hB (θ • d)
  have hm' := GaussianSmooth.mean_difference_bound (multivariateGaussian 0 (Q.residual η).val)
    (hs.of_le (by norm_num)) h0 h1 (θ • d) (η • d)
  have hk := mul_le_mul_of_nonneg_left (hK.norm_sub_le θ η) hBC
  calc
    _ ≤ ‖gaussianAverage (Q.residual θ).val H (θ • d) - gaussianAverage (Q.residual η).val H (θ • d)‖ +
        ‖gaussianAverage (Q.residual η).val H (θ • d) - gaussianAverage (Q.residual η).val H (η • d)‖ := by
      simpa only [dist_eq_norm] using dist_triangle (gaussianAverage (Q.residual θ).val H (θ • d))
        (gaussianAverage (Q.residual η).val H (θ • d)) (gaussianAverage (Q.residual η).val H (η • d))
    _ ≤ B * covarianceBoundConstant n * ‖(Q.residual θ).val - (Q.residual η).val‖ + L₁ * ‖θ • d - η • d‖ := add_le_add hc hm'
    _ ≤ B * covarianceBoundConstant n * ((K : ℝ) * ‖θ - η‖) + L₁ * ‖θ • d - η • d‖ := add_le_add_left hk _
    _ = T * |θ - η| := by
      rw [← sub_smul, norm_smul, Real.norm_eq_abs]
      dsimp [T]
      ring

/-- The total marked mean/covariance derivative of the actual affine
Gaussian curve integrates to its literal endpoint difference. -/
theorem integral_affine (Q : ProfileReserve A) {K : ℝ≥0}
    (hK : LipschitzWith K (fun θ => (Q.residual θ).val))
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ y, |F y| ≤ M)
    (base d : State n) (hd : d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (A 0)).range)
    (mark : ℝ → ℝ)
    (hmark : ∀ᵐ θ ∂volume, HasDerivAt (fun s => gaussianAverage (A s) F (base + s • d)) (mark θ) θ)
    (a b : ℝ) : IntervalIntegrable mark volume a b ∧
      (∫ θ in a..b, mark θ) = gaussianAverage (A b) F (base + b • d) - gaussianAverage (A a) F (base + a • d) := by
  obtain ⟨L, hL⟩ := exists_lipschitz_affine Q hK F hF M hM base d hd
  exact LipschitzIntegralIdentity.integral_eq_sub hL hmark a b

end SHE.GaussianRangeSmooth.ProfileReserve
