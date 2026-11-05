module

public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

/-! The final law argument on an actual space of probability measures.
The comparison estimates are explicit hypotheses. No SPDE estimate or
stochastic theorem is introduced as a global axiom. -/
noncomputable section
namespace SHE
open Filter Topology MeasureTheory

/-- A fixed real quantity approximated by the same sequence as another
quantity, with vanishing errors, must equal the other quantity.
The approximating sequence is not assumed to converge in advance. -/
theorem eq_of_common_approximations {a b : ℝ} {c e₁ e₂ : ℕ → ℝ}
    (h₁ : ∀ n, |a - c n| ≤ e₁ n) (h₂ : ∀ n, |b - c n| ≤ e₂ n)
    (he₁ : Tendsto e₁ atTop (𝓝 0)) (he₂ : Tendsto e₂ atTop (𝓝 0)) : a = b := by
  have hbound : ∀ n, |a - b| ≤ e₁ n + e₂ n := by
    intro n
    calc
      |a - b| = |(a - c n) + (c n - b)| := by congr 1; ring
      _ ≤ |a - c n| + |c n - b| := abs_add_le _ _
      _ = |a - c n| + |b - c n| := by rw [abs_sub_comm (c n) b]
      _ ≤ e₁ n + e₂ n := add_le_add (h₁ n) (h₂ n)
  have hle : |a - b| ≤ 0 := by
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds (by simpa using he₁.add he₂) hbound
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hle)

/-- A common canonical smooth law determines the original law once bounded
Lipschitz test errors vanish. This works on the integrated path space as well
as any metric Borel state space. -/
theorem laws_eq_of_common_comparisons
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (P Q : ProbabilityMeasure X) (ν : ℕ → ProbabilityMeasure X)
    (eP eQ : ℕ → ℝ)
    (heP : Tendsto eP atTop (𝓝 0)) (heQ : Tendsto eQ atTop (𝓝 0))
    (hP : ∀ (f : X → ℝ), (∃ C : ℝ, ∀ x y, dist (f x) (f y) ≤ C) →
      (∃ L, LipschitzWith L f) → ∀ n, |(∫ x, f x ∂P) - (∫ x, f x ∂(ν n))| ≤ eP n)
    (hQ : ∀ (f : X → ℝ), (∃ C : ℝ, ∀ x y, dist (f x) (f y) ≤ C) →
      (∃ L, LipschitzWith L f) → ∀ n, |(∫ x, f x ∂Q) - (∫ x, f x ∂(ν n))| ≤ eQ n) :
    P = Q := by
  have heq : ∀ (f : X → ℝ), (∃ C : ℝ, ∀ x y, dist (f x) (f y) ≤ C) →
      (∃ L, LipschitzWith L f) → (∫ x, f x ∂P) = (∫ x, f x ∂Q) := by
    intro f hf hl
    exact eq_of_common_approximations (hP f hf hl) (hQ f hf hl) heP heQ
  have ht : Tendsto (fun _ : ℕ => Q) atTop (𝓝 P) := by
    apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
    intro f hf hl
    rw [heq f hf hl]
    exact tendsto_const_nhds
  exact (tendsto_nhds_unique ht tendsto_const_nhds)

/-- The unnormalized tests above need a test-dependent multiplicative bound.
This version is useful for Girsanov/coupling estimates for general BL tests. -/
theorem laws_eq_of_scaled_common_comparisons
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (P Q : ProbabilityMeasure X) (ν : ℕ → ProbabilityMeasure X)
    (eP eQ : ℕ → ℝ)
    (heP : Tendsto eP atTop (𝓝 0)) (heQ : Tendsto eQ atTop (𝓝 0))
    (h : ∀ (f : X → ℝ), (∃ C : ℝ, ∀ x y, dist (f x) (f y) ≤ C) →
      (∃ L, LipschitzWith L f) → ∃ A : ℝ, ∀ n,
        |(∫ x, f x ∂P) - (∫ x, f x ∂(ν n))| ≤ A * eP n ∧
        |(∫ x, f x ∂Q) - (∫ x, f x ∂(ν n))| ≤ A * eQ n) : P = Q := by
  have heq : ∀ (f : X → ℝ), (∃ C : ℝ, ∀ x y, dist (f x) (f y) ≤ C) →
      (∃ L, LipschitzWith L f) → (∫ x, f x ∂P) = (∫ x, f x ∂Q) := by
    intro f hf hl
    obtain ⟨A, hA⟩ := h f hf hl
    apply eq_of_common_approximations (fun n => (hA n).1) (fun n => (hA n).2)
    · simpa using heP.const_mul A
    · simpa using heQ.const_mul A
  have ht : Tendsto (fun _ : ℕ => Q) atTop (𝓝 P) := by
    apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
    intro f hf hl
    rw [heq f hf hl]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique ht tendsto_const_nhds

/-- Deterministic exit-error limit used after stopped uniqueness is proved. -/
theorem localization_error_vanishes {A : ℝ} {exitP exitQ : ℕ → ℝ}
    (hP : Tendsto exitP atTop (𝓝 0)) (hQ : Tendsto exitQ atTop (𝓝 0)) :
    Tendsto (fun R => 2 * A * (exitP R + exitQ R)) atTop (𝓝 0) := by
  simpa using (hP.add hQ).const_mul (2 * A)

end SHE
