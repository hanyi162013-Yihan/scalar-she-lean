module

public import SHEStochastic.PastedCylinderMartingale
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.WeakLimitCylinderMartingale
open MeasureTheory ProbabilityTheory Filter StoppedPathPasting
open PastedGeneratorFunctional PastedCylinderMartingale PastedPastTests
open scoped NNReal Topology

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] (H : ℝ≥0)

/-- The entire canonical compensated cylinder value is bounded continuous
on continuous path space, including its time integral. -/
def functional (f b : BoundedContinuousFunction E ℝ) (t : Time H) :
    BoundedContinuousFunction (Path H E) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x ↦ value H f b x t)
    ((continuous_value H f b f.continuous b.continuous).comp
      (continuous_id.prodMk continuous_const))
    (2 * ‖f‖ + ‖b‖ * H) (fun x ↦ norm_value_bound H f b x t)

@[simp] theorem functional_apply (f b : BoundedContinuousFunction E ℝ)
    (t : Time H) (x : Path H E) : functional H f b t x = value H f b x t := rfl

/-- Weak limits retain all bounded continuous past-test identities.
This is a closure result, not an existence or uniqueness assumption. -/
theorem identity (f b : BoundedContinuousFunction E ℝ)
    (P : ℕ → ProbabilityMeasure (Path H E)) (Q : ProbabilityMeasure (Path H E))
    (hlim : Tendsto P atTop (𝓝 Q))
    (hP : ∀ k, Identity H f b (P k : Measure (Path H E))) :
    Identity H f b (Q : Measure (Path H E)) := by
  intro s t hst test htest
  let ψ := test * (functional H f b t - functional H f b s)
  have hl := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim ψ
  have hz : Tendsto (fun k ↦ ∫ x, ψ x ∂(P k : Measure (Path H E))) atTop (𝓝 0) := by
    convert (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0)) using 1
    funext k
    exact hP k s t hst test htest
  exact tendsto_nhds_unique hl hz

/-- Uniform generator perturbations control the compensated value on
every path. No moment bound on the path is required. -/
theorem generator_difference_bound (f b c : BoundedContinuousFunction E ℝ)
    (x : Path H E) (t : Time H) :
    ‖value H f b x t - value H f c x t‖ ≤ ‖b - c‖ * H := by
  have hb : IntervalIntegrable (fun r ↦ b (read H x r)) volume 0 t.val :=
    (b.continuous.comp (continuous_read H x)).intervalIntegrable _ _
  have hc : IntervalIntegrable (fun r ↦ c (read H x r)) volume 0 t.val :=
    (c.continuous.comp (continuous_read H x)).intervalIntegrable _ _
  have he : value H f b x t - value H f c x t =
      -(∫ r in 0..t.val, (b - c) (read H x r)) := by
    rw [show (∫ r in 0..t.val, (b - c) (read H x r)) =
      (∫ r in 0..t.val, b (read H x r)) - ∫ r in 0..t.val, c (read H x r) from
        intervalIntegral.integral_sub hb hc]
    unfold value
    ring
  rw [he, norm_neg]
  calc
    _ ≤ ‖b - c‖ * |t.val - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (fun r _ ↦ (b - c).norm_coe_le_norm _)
    _ ≤ ‖b - c‖ * H := by
      rw [sub_zero, abs_of_nonneg t.property.1]
      exact mul_le_mul_of_nonneg_left t.property.2 (norm_nonneg _)

/-- A weak-limit identity also survives a uniform perturbation of its
bounded continuous integrand. The probability measures may vary. -/
theorem integral_zero_of_uniform_approximation
    (P : ℕ → ProbabilityMeasure (Path H E)) (Q : ProbabilityMeasure (Path H E))
    (hlim : Tendsto P atTop (𝓝 Q))
    (ψ : BoundedContinuousFunction (Path H E) ℝ)
    (ψn : ℕ → BoundedContinuousFunction (Path H E) ℝ)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ k x, ‖ψ x - ψn k x‖ ≤ ε k)
    (hzero : ∀ k, (∫ x, ψn k x ∂(P k : Measure (Path H E))) = 0) :
    (∫ x, ψ x ∂(Q : Measure (Path H E))) = 0 := by
  have hb (k : ℕ) : ‖∫ x, ψ x ∂(P k : Measure (Path H E))‖ ≤ ε k := by
    have hi := norm_integral_le_of_norm_le_const
      (μ := (P k : Measure (Path H E))) (Filter.Eventually.of_forall (hbound k))
    rw [integral_sub (ψ.integrable _) ((ψn k).integrable _), hzero k,
      sub_zero, probReal_univ, mul_one] at hi
    exact hi
  have hz : Tendsto (fun k ↦ ∫ x, ψ x ∂(P k : Measure (Path H E))) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero (fun k ↦ norm_nonneg _) hb hε)
  exact tendsto_nhds_unique
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim ψ) hz

/-- Smooth bounded approximations can have different generators. Uniform
convergence of those generators is enough to pass their martingale
identities to the weak limit; no common probability space is needed. -/
theorem identity_of_generator_limit (f b : BoundedContinuousFunction E ℝ)
    (bn : ℕ → BoundedContinuousFunction E ℝ)
    (P : ℕ → ProbabilityMeasure (Path H E)) (Q : ProbabilityMeasure (Path H E))
    (hlim : Tendsto P atTop (𝓝 Q))
    (hb : Tendsto (fun k ↦ ‖b - bn k‖) atTop (𝓝 0))
    (hP : ∀ k, Identity H f (bn k) (P k : Measure (Path H E))) :
    Identity H f b (Q : Measure (Path H E)) := by
  intro s t hst test htest
  let ψ := test * (functional H f b t - functional H f b s)
  let ψn (k : ℕ) := test * (functional H f (bn k) t - functional H f (bn k) s)
  apply integral_zero_of_uniform_approximation H P Q hlim ψ ψn
    (fun k ↦ (2 * ‖test‖ * H) * ‖b - bn k‖)
  · simpa only [mul_zero] using tendsto_const_nhds.mul hb
  · intro k x
    change ‖test x * (value H f b x t - value H f b x s) -
      test x * (value H f (bn k) x t - value H f (bn k) x s)‖ ≤ _
    have he : test x * (value H f b x t - value H f b x s) -
        test x * (value H f (bn k) x t - value H f (bn k) x s) =
        test x * ((value H f b x t - value H f (bn k) x t) -
          (value H f b x s - value H f (bn k) x s)) := by ring
    rw [he, norm_mul]
    calc
      _ ≤ ‖test‖ * (‖b - bn k‖ * H + ‖b - bn k‖ * H) :=
        mul_le_mul (test.norm_coe_le_norm _) ((norm_sub_le _ _).trans
          (add_le_add (generator_difference_bound H f b (bn k) x t)
            (generator_difference_bound H f b (bn k) x s)))
          (norm_nonneg _) (norm_nonneg _)
      _ = _ := by ring
  · intro k
    exact hP k s t hst test htest

end SHEStochastic.WeakLimitCylinderMartingale
