module

public import SHE.PhysicalIto

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The exact expected physical one-step word identity. Martingale
centering is isolated as its ordinary stochastic input; integrability of
the actual remainder is proved from the physical identity. -/
noncomputable section
namespace SHE.PhysicalWordExpectation
open Set MeasureTheory ProbabilityTheory StoppedFourier
open GaussianItoTest PhysicalIto WordRecursion CovarianceEndpoint

abbrev State (n : ℕ) := WordRecursion.State n

theorem bounded_weight_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {H V : Ω → ℝ} (hH : Measurable H) (hV : Measurable V)
    {C M : ℝ} (hC : 0 ≤ C) (hHb : ∀ ω, ‖H ω‖ ≤ C) (hVb : ∀ ω, ‖V ω‖ ≤ M) :
    Integrable (fun ω => H ω * V ω) μ := by
  apply (integrable_const (C * M)).mono' (hH.mul hV).aestronglyMeasurable
  filter_upwards with ω
  change ‖H ω * V ω‖ ≤ C * M
  rw [norm_mul]
  exact mul_le_mul (hHb ω) (hVb ω) (norm_nonneg _) hC

/-- Any bounded initial measurable weight can be retained. Its product
with the genuine martingale term is the sole centering hypothesis.
The actual space-time insertion remainder is proved integrable. -/
theorem weighted_one_step_expectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {n : ℕ}
    (W : EndpointWindow n) (a : ℝ → ℝ) (ha : Measurable a)
    (U : Ω → ℝ → CircleL2) (X : Ω → ℝ × HeatCircle → ℝ)
    (hX : ∀ᵐ ω ∂μ, Measurable (X ω)) {A : ℝ} (hA : 0 ≤ A) (habound : ∀ z, |a z| ≤ A)
    (N : (ℝ → State n → ℝ) → Ω → ℝ)
    (hIto : FiniteItoInput μ (fun ω => observe (U ω) (X ω) W.observations)
      (fun ω t => CovarianceMatrix.densityMatrix (fun p => a (X ω p)) W.observations t) W.left W.right N)
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L B K : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖GaussianTaylor.hessian F z‖ ≤ B) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hHess : ∀ z w, ‖GaussianTaylor.hessian F w - GaussianTaylor.hessian F z‖ ≤ K * ‖w - z‖)
    (hYleft : Measurable (fun ω => observe (U ω) (X ω) W.observations W.left))
    (hYright : Measurable (fun ω => observe (U ω) (X ω) W.observations W.right))
    (H : Ω → ℝ) (hH : Measurable H) {C : ℝ} (hC : 0 ≤ C) (hHb : ∀ ω, ‖H ω‖ ≤ C)
    (hNint : Integrable (fun ω => H ω * N (backward W F) ω) μ)
    (hNzero : ∫ ω, H ω * N (backward W F) ω ∂μ = 0) :
    Integrable (fun ω => H ω * wordRemainder W a (U ω) (X ω) F) μ ∧
      (∫ ω, H ω * F (observe (U ω) (X ω) W.observations W.right) ∂μ) =
        (∫ ω, H ω * WordRecursion.gaussianSemigroup W.coefficient W.observations W.left W.right F
          (observe (U ω) (X ω) W.observations W.left) ∂μ) +
            ∫ ω, H ω * wordRemainder W a (U ω) (X ω) F ∂μ := by
  let V : Ω → ℝ := fun ω => F (observe (U ω) (X ω) W.observations W.right)
  let Q : Ω → ℝ := fun ω => backward W F W.left (observe (U ω) (X ω) W.observations W.left)
  let R : Ω → ℝ := fun ω => wordRemainder W a (U ω) (X ω) F
  have hV : Integrable (fun ω => H ω * V ω) μ := bounded_weight_integrable μ hH
    (hF.continuous.measurable.comp hYright) hC hHb (fun ω => hbound _)
  have hQ : Integrable (fun ω => H ω * Q ω) μ := bounded_weight_integrable μ hH
    (((backward_regular W hF hbound hD hDD hB hK hHess).state_smooth W.left).continuous.measurable.comp hYleft)
    hC hHb (fun ω => GaussianSmooth.average_norm_bound _ hbound _)
  have heq : (fun ω => H ω * R ω) =ᵐ[μ]
      fun ω => H ω * V ω - H ω * Q ω - H ω * N (backward W F) ω := by
    filter_upwards [physical_one_step μ W a ha U X hX hA habound N hIto hF hbound hD hDD hB hK hHess]
      with ω hω
    have hq : Q ω = WordRecursion.gaussianSemigroup W.coefficient W.observations W.left W.right F
        (observe (U ω) (X ω) W.observations W.left) := by
      dsimp only [Q]
      rw [backward_eq_semigroup W F ⟨le_rfl, W.ordered⟩]
    change H ω * R ω = H ω * V ω - H ω * Q ω - H ω * N (backward W F) ω
    change V ω = _ at hω
    rw [hω, ← hq]
    dsimp only [R]
    ring
  have hR : Integrable (fun ω => H ω * R ω) μ := ((hV.sub hQ).sub hNint).congr heq.symm
  refine ⟨hR, ?_⟩
  have he := integral_congr_ae heq
  have he₁ := integral_sub hV hQ
  have he₂ := integral_sub (hV.sub hQ) hNint
  simp only [Pi.sub_apply] at he₁ he₂
  rw [he₂, he₁, hNzero, sub_zero] at he
  have hqeq : (fun ω => H ω * Q ω) = fun ω => H ω * WordRecursion.gaussianSemigroup
      W.coefficient W.observations W.left W.right F
        (observe (U ω) (X ω) W.observations W.left) := by
    funext ω
    dsimp only [Q]
    rw [backward_eq_semigroup W F ⟨le_rfl, W.ordered⟩]
  rw [hqeq] at he
  change (∫ ω, H ω * V ω ∂μ) = _
  linarith only [he]

end SHE.PhysicalWordExpectation
