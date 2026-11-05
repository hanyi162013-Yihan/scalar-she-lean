module

public import SHE.ScalarRange
public import SHE.HeatChristoffel
public import SHE.GaussianGramScore

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Collision-uniform actual real Gaussian score envelopes from the physical
complex Fourier heat span. Real observation directions are handled through
the real part of the genuine continuous heat evaluation. -/
noncomputable section
namespace SHE.RealHeatScore
open Set MeasureTheory Real AddCircle SHE.HeatTorus SHE.HeatTorusKernel
  SHE.HeatProjection SHE.HeatChristoffel SHE.GaussianGramScore SHE.GaussianSmooth SHE.GaussianIncrement
open scoped InnerProductSpace Matrix.Norms.L2Operator

variable {q : ℕ} (t : Fin q → ℝ) (a : Fin q → UnitAddCircle) (ht : ∀ i, 0 < t i)

def realEvaluation (x : UnitAddCircle) : heatSpan t a →ₗ[ℝ] ℝ :=
  Complex.reCLM.toLinearMap.comp ((evaluation t a ht x).restrictScalars ℝ)

theorem realEvaluation_apply (x : UnitAddCircle) (f : heatSpan t a) :
    realEvaluation t a ht x f = (evaluation t a ht x f).re := rfl

/-- A real physical row has a genuine representative in the actual real
covariance range with the collision-uniform positive heat envelope. -/
theorem finite_real_heat_score_bound (q : ℕ) :
    ∃ h K : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < K ∧
      ∀ (t : Fin q → ℝ) (a : Fin q → UnitAddCircle) (ht : ∀ i, 0 < t i),
      (∀ i, t i ≤ h) →
      ∀ {D G : Type*} [AddCommGroup D] [Module ℝ D]
      [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
      (S : D →ₗ[ℝ] heatSpan t a) (C : D →ₗ[ℝ] G) [CompleteSpace C.range]
      (c : ℝ), 0 < c → (∀ z, c * ‖S z‖ ^ 2 ≤ ‖C z‖ ^ 2) →
      ∀ x : UnitAddCircle, ∃ m ∈ C.range,
      (∀ z, inner ℝ (C z) m = realEvaluation t a ht x (S z)) ∧
      ‖m‖ ^ 2 ≤ (K / c) * ∑ i, SHE.GlobalTorusHeatSpan.weight (t i) (a i) x := by
  obtain ⟨h, K, hh, hh1, hK, heval⟩ := finite_heat_evaluation_bound q
  refine ⟨h, K, hh, hh1, hK, ?_⟩
  intro t a ht hth D G _ _ _ _ _ S C _ c hc hcov x
  let W := K * ∑ i, SHE.GlobalTorusHeatSpan.weight (t i) (a i) x
  have hW : 0 ≤ W := by
    dsimp only [W]
    apply mul_nonneg hK.le
    apply Finset.sum_nonneg
    intro i _
    unfold SHE.GlobalTorusHeatSpan.weight
    positivity
  let B : D →ₗ[ℝ] ℝ := (realEvaluation t a ht x).comp S
  have hB (z : D) : ‖B z‖ ^ 2 ≤ (sqrt W) ^ 2 * ‖S z‖ ^ 2 := by
    rw [sq_sqrt hW]
    have hre : ‖B z‖ ≤ ‖evaluation t a ht x (S z)‖ :=
      Complex.abs_re_le_norm _
    calc
      _ ≤ ‖evaluation t a ht x (S z)‖ ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hre
      _ ≤ _ := by convert! heval t a ht hth (S z) x using 1; dsimp only [W]; ring
  obtain ⟨T, hT, hTC, _⟩ := ScalarRange.factorization_of_gram_dominance C B
    (fun z => ‖S z‖ ^ 2) hc (sqrt_nonneg _) hB hcov
  obtain ⟨m, hm, hpair, hn⟩ := ScalarRange.adjoint_representer C.range T (1 : ℝ)
  refine ⟨m, hm, ?_, ?_⟩
  · intro z
    have he := hpair (C z) (LinearMap.mem_range_self C z)
    rw [hTC] at he
    simpa only [RCLike.inner_apply, conj_trivial, mul_one, one_mul, B, LinearMap.comp_apply] using he
  · have hnorm : ‖m‖ ≤ sqrt W / sqrt c := by
      simpa only [norm_one, mul_one] using hn.trans
        (mul_le_mul_of_nonneg_right hT (norm_nonneg (1 : ℝ)))
    have hs := (sq_le_sq₀ (norm_nonneg m) (div_nonneg (sqrt_nonneg _) (sqrt_nonneg _))).mpr hnorm
    rw [div_pow, sq_sqrt hW, sq_sqrt hc.le] at hs
    convert! hs using 1
    dsimp only [W]
    ring

/-- The preceding physical envelope controls the actual second scalar
Gaussian score for every fixed moment, via the genuine real covariance Gram. -/
theorem finite_real_gaussian_score_envelope (q : ℕ) :
    ∃ h K : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < K ∧
      ∀ (t : Fin q → ℝ) (a : Fin q → UnitAddCircle) (ht : ∀ i, 0 < t i),
      (∀ i, t i ≤ h) →
      ∀ {n : ℕ} {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
      (v : Fin n → G) (S : State n →ₗ[ℝ] heatSpan t a) (c : ℝ), 0 < c →
      (∀ z, c * ‖S z‖ ^ 2 ≤ ‖featureSynthesis v z‖ ^ 2) →
      ∀ (x : UnitAddCircle) (d : State n),
      (∀ z, realEvaluation t a ht x (S z) = inner ℝ z d) →
      ∃ m ∈ (featureSynthesis v).range,
        (∀ z, inner ℝ (featureSynthesis v z) m = inner ℝ z d) ∧
        ‖m‖ ^ 2 ≤ (K / c) * ∑ i, SHE.GlobalTorusHeatSpan.weight (t i) (a i) x ∧
        ∀ {F : State n → ℝ}, ContDiff ℝ 2 F → ∀ {M L B : ℝ},
          (∀ z, ‖F z‖ ≤ M) → (∀ z, ‖fderiv ℝ F z‖ ≤ L) →
          (∀ z, ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ B) → ∀ z,
          |fderiv ℝ (fderiv ℝ (GaussianSmooth.average (ProbabilityTheory.multivariateGaussian 0
            (Matrix.gram ℝ v)) F)) z d d| ≤
            2 * M * ((K / c) * ∑ i, SHE.GlobalTorusHeatSpan.weight (t i) (a i) x) := by
  obtain ⟨h, K, hh, hh1, hK, hscore⟩ := finite_real_heat_score_bound q
  refine ⟨h, K, hh, hh1, hK, ?_⟩
  intro t a ht hth n G _ _ _ v S c hc hcov x d hrow
  obtain ⟨m, hm, hp, hn⟩ := hscore t a ht hth S (featureSynthesis v) c hc hcov x
  have hpair : ∀ z, inner ℝ (featureSynthesis v z) m = inner ℝ z d :=
    fun z => (hp z).trans (hrow z)
  refine ⟨m, hm, hpair, hn, ?_⟩
  intro F hF M L B hbound hD hDD z
  have hM : 0 ≤ M := (norm_nonneg (F 0)).trans (hbound 0)
  exact (hessian_gaussian_gram_physical_bound v hm hpair hF hbound hD hDD z).trans
    (mul_le_mul_of_nonneg_left hn (by positivity))

end SHE.RealHeatScore
