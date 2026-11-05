module

public import SHEStochastic.WeakLimitMomentTests
public import SHEStochastic.SubGaussianFourthMoment

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.WeakLimitSubGaussian
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

variable {X : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- Sub-Gaussian control passes to a weak joint path limit, with the
same variance parameter. Portmanteau supplies exponential integrability. -/
theorem limit (P : ℕ → ProbabilityMeasure X) (Q : ProbabilityMeasure X)
    (hlim : Tendsto P atTop (𝓝 Q)) (f : X → ℝ) (hf : Continuous f) (c : ℝ≥0)
    (h : ∀ k, HasSubgaussianMGF f c (P k : Measure X)) :
    HasSubgaussianMGF f c (Q : Measure X) := by
  have he (a : ℝ) := WeakLimitMomentTests.nonnegative_bound P Q hlim
    (fun x ↦ Real.exp (a*f x)) (Real.continuous_exp.comp (continuous_const.mul hf))
    (fun x ↦ (Real.exp_pos _).le) (Real.exp ((c : ℝ)*a^2/2))
    (fun k ↦ (h k).integrable_exp_mul a) (fun k ↦ (h k).mgf_le a)
  exact ⟨fun a ↦ (he a).1, fun a ↦ (he a).2⟩

/-- One sub-Gaussian bound supplies the second-moment cap needed by
the weak-limit martingale theorem, with no moment of the initial state. -/
theorem square_bound (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF f c μ) :
    MemLp f 2 μ ∧ (∫ x, f x^2 ∂μ) ≤ 1+48*Real.exp (1/2 : ℝ)*(c : ℝ)^2 := by
  have h4 : MemLp f 4 μ := by simpa using h.memLp (4 : ℝ≥0)
  have h2 : MemLp f 2 μ := h4.mono_exponent (by norm_num)
  have hi4 : Integrable (fun x ↦ f x^4) μ := by
    exact (h4.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)).mono'
      (h.aestronglyMeasurable.pow 4) (Filter.Eventually.of_forall fun x ↦ by rw [norm_pow])
  refine ⟨h2, ?_⟩
  calc
    _ ≤ ∫ x, 1+f x^4 ∂μ := integral_mono h2.integrable_sq ((integrable_const 1).add hi4)
      (fun x ↦ by nlinarith [sq_nonneg (f x^2-1)])
    _ = 1+(∫ x, f x^4 ∂μ) := by rw [integral_add (integrable_const 1) hi4]; simp
    _ ≤ _ := by linarith [SubGaussianFourthMoment.integral_fourth_le h]

end SHEStochastic.WeakLimitSubGaussian
