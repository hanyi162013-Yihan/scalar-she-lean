module

public import SHE.HistoryFrames

@[expose] public section
set_option autoImplicit false
noncomputable section

/-! Real and complex covariance-range factorizations on the actual quotient,
with no invertibility assumption. -/
namespace SHE.ScalarRange
open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]

theorem factorization_of_bound {D H E : Type*} [AddCommGroup D] [Module 𝕜 D]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (A : D →ₗ[𝕜] H) (B : D →ₗ[𝕜] E) [CompleteSpace A.range]
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ x, ‖B x‖ ≤ K * ‖A x‖) :
    ∃ T : H →L[𝕜] E, ‖T‖ ≤ K ∧ (∀ x, T (A x) = B x) ∧
      T = T.comp A.range.starProjection := by
  have hker : A.ker ≤ B.ker := by
    intro x hx
    change B x = 0
    have hx' : A x = 0 := hx
    apply norm_eq_zero.mp
    have hh := hbound x
    rw [hx', norm_zero, mul_zero] at hh
    exact le_antisymm hh (norm_nonneg _)
  let L : A.range →ₗ[𝕜] E :=
    (A.ker.liftQ B hker).comp A.quotKerEquivRange.symm.toLinearMap
  have hL : ∀ x, L ⟨A x, LinearMap.mem_range_self A x⟩ = B x := by
    intro x
    simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hb : ∀ y : A.range, ‖L y‖ ≤ K * ‖y‖ := by
    intro y
    obtain ⟨x, hx⟩ := y.property
    have hy : y = ⟨A x, LinearMap.mem_range_self A x⟩ := Subtype.ext hx.symm
    rw [hy, hL]
    exact hbound x
  let S : A.range →L[𝕜] E := L.mkContinuous K hb
  let T : H →L[𝕜] E := S.comp A.range.orthogonalProjectionOnto
  refine ⟨T, ?_, ?_, ?_⟩
  · calc
      ‖T‖ ≤ ‖S‖ * ‖A.range.orthogonalProjectionOnto‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ K * 1 := mul_le_mul (LinearMap.mkContinuous_norm_le L hK hb)
        A.range.orthogonalProjectionOnto_norm_le
        (norm_nonneg A.range.orthogonalProjectionOnto) hK
      _ = K := mul_one _
  · intro x
    change S (A.range.orthogonalProjectionOnto (A x)) = B x
    have hp : A.range.orthogonalProjectionOnto (A x) = ⟨A x, LinearMap.mem_range_self A x⟩ :=
      A.range.orthogonalProjectionOnto_mem_subspace_eq_self ⟨A x, LinearMap.mem_range_self A x⟩
    rw [hp]
    exact hL x
  · ext y
    change S (A.range.orthogonalProjectionOnto y) =
      S (A.range.orthogonalProjectionOnto (A.range.starProjection y))
    simp only [Submodule.starProjection_apply, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

theorem factorization_of_gram_dominance {D G E : Type*} [AddCommGroup D] [Module 𝕜 D]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (C : D →ₗ[𝕜] G) (B : D →ₗ[𝕜] E) [CompleteSpace C.range]
    (energy : D → ℝ) {c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K)
    (hB : ∀ z, ‖B z‖ ^ 2 ≤ K ^ 2 * energy z)
    (hcov : ∀ z, c * energy z ≤ ‖C z‖ ^ 2) :
    ∃ T : G →L[𝕜] E, ‖T‖ ≤ K / Real.sqrt c ∧ (∀ z, T (C z) = B z) ∧
      T = T.comp C.range.starProjection := by
  apply factorization_of_bound C B (div_nonneg hK (Real.sqrt_nonneg _))
  intro z
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, div_pow, Real.sq_sqrt hc.le]
  have he : energy z ≤ ‖C z‖ ^ 2 / c :=
    (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hcov z)
  calc
    ‖B z‖ ^ 2 ≤ K ^ 2 * energy z := hB z
    _ ≤ K ^ 2 * (‖C z‖ ^ 2 / c) := mul_le_mul_of_nonneg_left he (sq_nonneg _)
    _ = _ := by ring

theorem adjoint_representer {G E : Type*}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (K : Submodule 𝕜 G) [CompleteSpace K] (T : G →L[𝕜] E) (d : E) :
    ∃ m ∈ K, (∀ y ∈ K, inner 𝕜 y m = inner 𝕜 (T y) d) ∧ ‖m‖ ≤ ‖T‖ * ‖d‖ := by
  let m : G := K.starProjection (ContinuousLinearMap.adjoint T d)
  refine ⟨m, (K.orthogonalProjectionOnto _).property, ?_, ?_⟩
  · intro y hy
    change inner 𝕜 y (K.starProjection (ContinuousLinearMap.adjoint T d)) = _
    rw [← K.inner_starProjection_left_eq_right, K.starProjection_eq_self_iff.mpr hy,
      ContinuousLinearMap.adjoint_inner_right]
  · calc
      ‖m‖ ≤ ‖ContinuousLinearMap.adjoint T d‖ := K.norm_orthogonalProjectionOnto_apply_le _
      _ ≤ ‖ContinuousLinearMap.adjoint T‖ * ‖d‖ := (ContinuousLinearMap.adjoint T).le_opNorm d
      _ = _ := by rw [ContinuousLinearMap.adjoint.norm_map]

end SHE.ScalarRange
