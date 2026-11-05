module

public import SHE.HeatChristoffelTransfer

/-! Actual covariance-range mean representatives retain the orthogonal
projection onto the physical heat span. Haar integration therefore keeps
a genuine heat operator on the sole signed L² input. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.HeatCovarianceMean
open MeasureTheory Set Real AddCircle SHE.HeatTorus SHE.HeatTorusKernel
  SHE.HeatProjection
open scoped InnerProductSpace

theorem range_representer_unique {D G : Type*} [AddCommGroup D] [Module ℂ D]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (C : D →ₗ[ℂ] G) {m₁ m₂ : G} (hm₁ : m₁ ∈ C.range) (hm₂ : m₂ ∈ C.range)
    (hpair : ∀ z, inner ℂ (C z) m₁ = inner ℂ (C z) m₂) : m₁ = m₂ := by
  obtain ⟨z, hz⟩ := C.range.sub_mem hm₁ hm₂
  have hzero : inner ℂ (m₁ - m₂) (m₁ - m₂) = 0 := by
    nth_rw 1 [← hz]
    rw [inner_sub_right, hpair z, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)

/-- The Riesz vector for a physical mean direction needs only the actual
heat-span projection of the signed input. -/
theorem mean_representer_projection_bound {D G : Type*}
    [AddCommGroup D] [Module ℂ D]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {q : ℕ} (t : Fin q → ℝ) (a : Fin q → UnitAddCircle)
    (S : D →ₗ[ℂ] CircleL2) (C : D →ₗ[ℂ] G) [CompleteSpace C.range]
    (hspan : ∀ z, S z ∈ heatSpan t a) {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ z, ‖S z‖ ≤ L * ‖C z‖) (d : CircleL2) :
    ∃ m ∈ C.range, (∀ z, inner ℂ (C z) m = inner ℂ (S z) d) ∧
      ‖m‖ ≤ L * ‖(heatSpan t a).starProjection d‖ := by
  let S' : D →ₗ[ℂ] heatSpan t a := S.codRestrict _ hspan
  obtain ⟨T, hT, hTC, _⟩ := SHE.StoppedFourier.range_factorization_of_bound C S' hL hbound
  let d' : heatSpan t a := (heatSpan t a).orthogonalProjectionOnto d
  obtain ⟨m, hm, hp, hn⟩ := SHE.StoppedFourier.range_adjoint_representer C.range T d'
  refine ⟨m, hm, ?_, ?_⟩
  · intro z
    rw [hp _ (LinearMap.mem_range_self C z), hTC]
    exact (heatSpan t a).inner_orthogonalProjectionOnto_eq_of_mem_left (S' z) d
  · exact hn.trans (mul_le_mul_of_nonneg_right hT (norm_nonneg d'))

/-- The integrated bound is derived from the actual Riesz characterization,
not from a postulated bound on a score field. Covariances may vary with the
translation. The measurability premise concerns the actual representative
field only. -/
theorem translated_covariance_mean_bound (q : ℕ) :
    ∃ h K θ : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < K ∧ 0 < θ ∧
      ∀ (t : Fin q → ℝ) (a : Fin q → UnitAddCircle), (∀ i, 0 < t i) → (∀ i, t i ≤ h) →
      ∀ (w M : ℝ), 0 < w → 1 ≤ M → (∀ i, w ≤ t i) → (∀ i, t i ≤ M * w) →
      ∀ {D G : Type*} [AddCommGroup D] [Module ℂ D]
      [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
      (S : UnitAddCircle → D →ₗ[ℂ] CircleL2) (C : UnitAddCircle → D →ₗ[ℂ] G)
      [∀ x, CompleteSpace (C x).range] (L : ℝ), 0 ≤ L →
      (∀ x z, S x z ∈ heatSpan t (fun i => a i + x)) →
      (∀ x z, ‖S x z‖ ≤ L * ‖C x z‖) →
      ∀ (d : CircleL2) (m : UnitAddCircle → G), AEStronglyMeasurable m haarAddCircle →
      (∀ x, m x ∈ (C x).range) →
      (∀ x z, inner ℂ (C x z) (m x) = inner ℂ (S x z) d) →
      Integrable (fun x => ‖m x‖ ^ 2) haarAddCircle ∧
      (∫ x : UnitAddCircle, ‖m x‖ ^ 2 ∂haarAddCircle) ≤
        K * L ^ 2 * sqrt M * sqrt w * ‖SHE.CircleHeat.heat (θ * w) d‖ ^ 2 := by
  obtain ⟨h, K, θ, hh, hh1, hK, hθ, hproj⟩ := translated_heat_span_projection_bound q
  refine ⟨h, K, θ, hh, hh1, hK, hθ, ?_⟩
  intro t a ht hth w M hw hM hlo hhi D G _ _ _ _ _ S C _ L hL hspan hbound d m hm hmr hmp
  obtain ⟨hpi, hpbound⟩ := hproj t a ht hth w M hw hM hlo hhi d
  have hpoint (x : UnitAddCircle) :
      ‖m x‖ ^ 2 ≤ L ^ 2 * ‖(heatSpan t (fun i => a i + x)).starProjection d‖ ^ 2 := by
    obtain ⟨v, hv, hp, hn⟩ := mean_representer_projection_bound t (fun i => a i + x)
      (S x) (C x) (hspan x) hL (hbound x) d
    have heq : m x = v := range_representer_unique (C x) (hmr x) hv
      (fun z => (hmp x z).trans (hp z).symm)
    rw [heq]
    have hs := (sq_le_sq₀ (norm_nonneg v) (mul_nonneg hL (norm_nonneg _))).mpr hn
    simpa only [mul_pow] using hs
  have hi : Integrable (fun x => ‖m x‖ ^ 2) haarAddCircle := by
    apply (hpi.const_mul (L ^ 2)).mono' (hm.norm.pow 2)
    exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint x)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x : UnitAddCircle, L ^ 2 *
        ‖(heatSpan t (fun i => a i + x)).starProjection d‖ ^ 2 ∂haarAddCircle :=
      integral_mono hi (hpi.const_mul _) hpoint
    _ = L ^ 2 * (∫ x : UnitAddCircle,
        ‖(heatSpan t (fun i => a i + x)).starProjection d‖ ^ 2 ∂haarAddCircle) := integral_const_mul _ _
    _ ≤ L ^ 2 * (K * sqrt M * sqrt w * ‖SHE.CircleHeat.heat (θ * w) d‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hpbound (sq_nonneg _)
    _ = _ := by ring

end SHE.HeatCovarianceMean
