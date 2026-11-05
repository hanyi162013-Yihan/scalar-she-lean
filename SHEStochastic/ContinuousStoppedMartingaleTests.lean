module

public import BrownianMotion.StochasticIntegral.OptionalSampling
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.ContinuousStoppedMartingaleTests
open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)

/-- The bounded past-test identity also holds for vector and complex
martingales, using real scalar multiplication. -/
theorem weighted_increment_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (M : ℝ≥0 → Ω → E) (hM : Martingale M F μ)
    (s t : ℝ≥0) (hst : s ≤ t) (test : Ω → ℝ)
    (htest : StronglyMeasurable[F s] test) (C : ℝ)
    (hbound : ∀ ω, ‖test ω‖ ≤ C) :
    (∫ ω, test ω • (M t ω - M s ω) ∂μ) = 0 := by
  have hi := (hM.integrable t).sub (hM.integrable s)
  have hip : Integrable (fun ω ↦ test ω • (M t ω - M s ω)) μ :=
    hi.bdd_smul C (htest.mono (F.le s)).aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  have hc : μ[fun ω ↦ M t ω - M s ω | F s] =ᵐ[μ] fun _ ↦ (0 : E) := by
    apply (condExp_sub (hM.integrable t) (hM.integrable s) (F s)).trans
    have hs : μ[M s | F s] = M s :=
      condExp_of_stronglyMeasurable (F.le s) (hM.stronglyAdapted s) (hM.integrable s)
    filter_upwards [hM.condExp_ae_eq hst] with ω hω
    simp only [Pi.sub_apply, hs, hω, sub_self]
  have hp := condExp_smul_of_aestronglyMeasurable_left
    htest.aestronglyMeasurable hip hi
  change μ[fun ω ↦ test ω • (M t ω - M s ω) | F s] =ᵐ[μ]
    fun ω ↦ test ω • μ[fun ω ↦ M t ω - M s ω | F s] ω at hp
  calc
    _ = ∫ ω, μ[fun ω ↦ test ω • (M t ω - M s ω) | F s] ω ∂μ :=
      (integral_condExp (F.le s)).symm
    _ = 0 := by
      have hz : μ[fun ω ↦ test ω • (M t ω - M s ω) | F s] =ᵐ[μ] fun _ ↦ (0 : E) := by
        filter_upwards [hp, hc] with ω hω hcω
        rw [hω, hcω, smul_zero]
      rw [integral_congr_ae hz, integral_zero]

/-- Optional stopping for the same vector-valued past-test identity. -/
theorem stopped_weighted_increment_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (M : ℝ≥0 → Ω → E) (hM : Martingale M F μ)
    (hcont : ∀ ω, Continuous (fun t ↦ M t ω))
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime F τ)
    (s t : ℝ≥0) (hst : s ≤ t) (test : Ω → ℝ)
    (htest : StronglyMeasurable[F s] test) (C : ℝ)
    (hbound : ∀ ω, ‖test ω‖ ≤ C) :
    (∫ ω, test ω • (stoppedProcess M τ t ω - stoppedProcess M τ s ω) ∂μ) = 0 :=
  weighted_increment_smul μ F (stoppedProcess M τ)
    (hM.stoppedProcess (fun ω q ↦ (hcont ω).continuousAt.continuousWithinAt) hτ)
    s t hst test htest C hbound

/-- The ordinary bounded past-test identity, directly from the
martingale conditional expectation. -/
theorem weighted_increment (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M F μ)
    (s t : ℝ≥0) (hst : s ≤ t) (test : Ω → ℝ)
    (htest : StronglyMeasurable[F s] test) (C : ℝ)
    (hbound : ∀ ω, ‖test ω‖ ≤ C) :
    (∫ ω, test ω * (M t ω - M s ω) ∂μ) = 0 := by
  simpa only [smul_eq_mul] using weighted_increment_smul μ F M hM s t hst test htest C hbound

/-- Continuous martingales remain martingales at arbitrary stopping
times. This reuses the public dyadic approximation and optional-sampling
proof, scoped to its proved martingale declarations. -/
theorem stopped_weighted_increment (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M F μ)
    (hcont : ∀ ω, Continuous (fun t ↦ M t ω))
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime F τ)
    (s t : ℝ≥0) (hst : s ≤ t) (test : Ω → ℝ)
    (htest : StronglyMeasurable[F s] test) (C : ℝ)
    (hbound : ∀ ω, ‖test ω‖ ≤ C) :
    (∫ ω, test ω * (stoppedProcess M τ t ω - stoppedProcess M τ s ω) ∂μ) = 0 :=
  weighted_increment μ F (stoppedProcess M τ)
    (hM.stoppedProcess (fun ω q ↦ (hcont ω).continuousAt.continuousWithinAt) hτ)
    s t hst test htest C hbound

end SHEStochastic.ContinuousStoppedMartingaleTests
