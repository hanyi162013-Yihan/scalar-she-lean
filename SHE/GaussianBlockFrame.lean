module

public import SHE.RealHeatCovarianceMean

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

/-! Actual real covariance-range combination of finitely many Gaussian
blocks. The block frame controls the canonical full score variance with
the sum of the physical block energies, also at singular ranks. -/
namespace SHE.GaussianBlockFrame
open Set MeasureTheory AddCircle Real HeatTorus HeatProjection GaussianIncrement
  GaussianGramScore MeasurableGaussianScores RealHeatCovarianceMean ScalarRange
open scoped InnerProductSpace

variable {g : ℕ} {D H G : Type*} [AddCommGroup D] [Module ℝ D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

def blockSynthesis (C : Fin g → D →ₗ[ℝ] G) : D →ₗ[ℝ] PiLp 2 (fun _ : Fin g => G) where
  toFun z := WithLp.toLp 2 (fun j => C j z)
  map_add' z w := by
    apply (WithLp.equiv 2 (Fin g → G)).injective
    funext j
    exact map_add (C j) z w
  map_smul' b z := by
    apply (WithLp.equiv 2 (Fin g → G)).injective
    funext j
    exact map_smul (C j) b z

omit [CompleteSpace G] in
theorem blockSynthesis_norm_sq (C : Fin g → D →ₗ[ℝ] G) (z : D) :
    ‖blockSynthesis C z‖ ^ 2 = ∑ j, ‖C j z‖ ^ 2 := by
  exact PiLp.norm_sq_eq_of_L2 _ _

omit [CompleteSpace G] in
theorem combine_representers (A : D →ₗ[ℝ] H) [CompleteSpace A.range]
    (C : Fin g → D →ₗ[ℝ] G) (m : Fin g → G) {c : ℝ} (hc : 0 < c)
    (hframe : ∀ z, c * (∑ j, ‖C j z‖ ^ 2) ≤ ‖A z‖ ^ 2) :
    ∃ v ∈ A.range,
      (∀ z, inner ℝ (A z) v = ∑ j, inner ℝ (C j z) (m j)) ∧
      ‖v‖ ^ 2 ≤ (∑ j, ‖m j‖ ^ 2) / c := by
  let b : PiLp 2 (fun _ : Fin g => G) := WithLp.toLp 2 m
  let B : D →ₗ[ℝ] ℝ := (innerSL ℝ b).toLinearMap.comp (blockSynthesis C)
  have hB (z : D) : ‖B z‖ ^ 2 ≤ ‖b‖ ^ 2 * (∑ j, ‖C j z‖ ^ 2) := by
    have hi := norm_inner_le_norm (𝕜 := ℝ) b (blockSynthesis C z)
    have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg b) (norm_nonneg _))).mpr hi
    rw [mul_pow, blockSynthesis_norm_sq] at hs
    exact hs
  obtain ⟨T, hT, hTA, _⟩ := ScalarRange.factorization_of_gram_dominance A B
    (fun z => ∑ j, ‖C j z‖ ^ 2) hc (norm_nonneg b) hB hframe
  obtain ⟨v, hv, hp, hn⟩ := ScalarRange.adjoint_representer A.range T (1 : ℝ)
  refine ⟨v, hv, ?_, ?_⟩
  · intro z
    rw [hp _ (LinearMap.mem_range_self A z), hTA]
    simp only [RCLike.inner_apply, conj_trivial, one_mul]
    change inner ℝ b (blockSynthesis C z) = ∑ j, inner ℝ (C j z) (m j)
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl (fun j _ => real_inner_comm _ _)
  · have hn' : ‖v‖ ≤ ‖b‖ / sqrt c := by
      simp only [norm_one, mul_one] at hn
      exact hn.trans hT
    have hs := (sq_le_sq₀ (norm_nonneg v) (div_nonneg (norm_nonneg b) (sqrt_nonneg _))).mpr hn'
    rw [div_pow, sq_sqrt hc.le, PiLp.norm_sq_eq_of_L2] at hs
    exact hs

theorem block_scoreVariance_projection_bound {n q : ℕ}
    (t : Fin g → Fin q → ℝ) (a : Fin g → Fin q → UnitAddCircle)
    (v : Fin n → H) (C : Fin g → State n →ₗ[ℝ] G)
    (S : Fin g → State n →ₗ[ℝ] CircleL2) (L : Fin g → ℝ)
    (hL : ∀ j, 0 ≤ L j) (hspan : ∀ j z, S j z ∈ heatSpan (t j) (a j))
    (hbound : ∀ j z, ‖S j z‖ ≤ L j * ‖C j z‖) {c : ℝ} (hc : 0 < c)
    (hframe : ∀ z, c * (∑ j, ‖C j z‖ ^ 2) ≤ ‖featureSynthesis v z‖ ^ 2)
    (d : CircleL2) :
    meanDirection (∑ j, S j) d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.gram ℝ v)).range ∧
      scoreVariance (Matrix.gram ℝ v) (meanDirection (∑ j, S j) d) ≤
        (∑ j, L j ^ 2 * ‖(heatSpan (t j) (a j)).starProjection d‖ ^ 2) / c := by
  choose m hm hp hn using fun j => mean_representer_projection_bound (t j) (a j)
    (S j) (C j) (hspan j) (hL j) (hbound j) d
  obtain ⟨u, hu, hup, hub⟩ := combine_representers (featureSynthesis v) C m hc hframe
  have hpair (z : State n) : inner ℝ (featureSynthesis v z) u =
      inner ℝ z (meanDirection (∑ j, S j) d) := by
    rw [hup, inner_meanDirection]
    simp only [LinearMap.sum_apply, sum_inner, Complex.re_sum]
    exact Finset.sum_congr rfl (fun j _ => hp j z)
  refine ⟨physical_direction_mem_range v hu hpair, ?_⟩
  rw [physical_scoreVariance_eq v hu hpair]
  apply hub.trans
  apply div_le_div_of_nonneg_right _ hc.le
  apply Finset.sum_le_sum
  intro j _
  have hs := (sq_le_sq₀ (norm_nonneg (m j))
    (mul_nonneg (hL j) (norm_nonneg _))).mpr (hn j)
  simpa only [mul_pow] using hs

end SHE.GaussianBlockFrame
