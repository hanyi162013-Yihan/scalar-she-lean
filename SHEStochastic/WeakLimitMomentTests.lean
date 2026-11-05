module

public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.WeakLimitMomentTests
open MeasureTheory Filter
open scoped Topology ENNReal

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace.MetrizableSpace X]
  (P : ℕ → ProbabilityMeasure X) (Q : ProbabilityMeasure X)
  (hlim : Tendsto P atTop (𝓝 Q))

include hlim in
/-- A uniform expectation bound for a nonnegative continuous function
survives weak convergence, including its integrability. -/
theorem nonnegative_bound (f : X → ℝ) (hf : Continuous f) (hpos : ∀ x, 0 ≤ f x) (C : ℝ)
    (hi : ∀ k, Integrable f (P k : Measure X))
    (hb : ∀ k, (∫ x, f x ∂(P k : Measure X)) ≤ C) :
    Integrable f (Q : Measure X) ∧ (∫ x, f x ∂(Q : Measure X)) ≤ C := by
  have hp := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    hf hpos
    (fun A hA ↦ ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hA)
  have hB (k : ℕ) : (∫⁻ x, ENNReal.ofReal (f x) ∂(P k : Measure X)) ≤ ENNReal.ofReal C := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hi k) (Filter.Eventually.of_forall hpos)]
    exact ENNReal.ofReal_le_ofReal (hb k)
  have hL : (∫⁻ x, ENNReal.ofReal (f x) ∂(Q : Measure X)) ≤ ENNReal.ofReal C := by
    exact hp.trans (liminf_le_of_frequently_le' (Filter.Eventually.of_forall hB).frequently)
  have hInt := (lintegral_ofReal_ne_top_iff_integrable
    hf.stronglyMeasurable.aestronglyMeasurable (Filter.Eventually.of_forall hpos)).mp
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hL)
  refine ⟨hInt, ?_⟩
  have hC : 0 ≤ C := (integral_nonneg hpos).trans (hb 0)
  rw [← ofReal_integral_eq_lintegral_ofReal hInt
    (Filter.Eventually.of_forall hpos), ENNReal.ofReal_le_ofReal_iff hC] at hL
  exact hL

include hlim in
theorem square_bound (f : X → ℝ) (hf : Continuous f) (C : ℝ)
    (hi : ∀ k, Integrable (fun x ↦ f x ^ 2) (P k : Measure X))
    (hb : ∀ k, (∫ x, f x ^ 2 ∂(P k : Measure X)) ≤ C) :
    Integrable (fun x ↦ f x ^ 2) (Q : Measure X) ∧
      (∫ x, f x ^ 2 ∂(Q : Measure X)) ≤ C :=
  nonnegative_bound P Q hlim (fun x ↦ f x^2) (hf.pow 2) (fun x ↦ sq_nonneg _) C hi hb

def clip (f : X → ℝ) (hf : Continuous f) (R : ℝ) (hR : 0 ≤ R) :
    BoundedContinuousFunction X ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x ↦ max (-R) (min R (f x)))
    (continuous_const.max (continuous_const.min hf)) R (fun x ↦ by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩)

theorem clip_error (x R : ℝ) (hR : 0 < R) :
    |x-max (-R) (min R x)| ≤ x^2/R := by
  by_cases hlow : x < -R
  · rw [min_eq_right (by linarith), max_eq_left hlow.le,
      abs_of_nonpos (by linarith), le_div_iff₀ hR]
    nlinarith [sq_nonneg (x+R)]
  · by_cases hhigh : R < x
    · rw [min_eq_left hhigh.le, max_eq_right (by linarith),
        abs_of_nonneg (by linarith), le_div_iff₀ hR]
      nlinarith [sq_nonneg (x-R)]
    · rw [min_eq_right (le_of_not_gt hhigh), max_eq_right (le_of_not_gt hlow),
        sub_self, abs_zero]
      exact div_nonneg (sq_nonneg x) hR.le

/-- Truncation has a uniform L1 error controlled by the second moment.
It applies to the Fourier fluctuation and its quadratic test functions. -/
theorem integral_clip_error (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℝ) (hf : Continuous f) (hInt : Integrable (fun x ↦ f x^2) μ)
    (C R : ℝ) (hC : (∫ x, f x^2 ∂μ) ≤ C) (hR : 0 < R) :
    ‖(∫ x, f x ∂μ)-(∫ x, clip f hf R hR.le x ∂μ)‖ ≤ C/R := by
  have hM : MemLp f 2 μ := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr hInt
  rw [← integral_sub (hM.integrable one_le_two) ((clip f hf R hR.le).integrable μ)]
  calc
    _ ≤ ∫ x, f x^2/R ∂μ := norm_integral_le_of_norm_le
      (hInt.div_const R) (Filter.Eventually.of_forall fun x ↦ clip_error (f x) R hR)
    _ = (∫ x, f x^2 ∂μ)/R := integral_div R _
    _ ≤ C/R := div_le_div_of_nonneg_right hC hR.le

include hlim in
/-- Weak convergence plus a uniform second moment permits continuous
unbounded tests. Applying this to quadratic Fourier tests uses their
already available fourth moments and avoids a new cutoff calculus. -/
theorem integral_tendsto (f : X → ℝ) (hf : Continuous f) (C : ℝ)
    (hi : ∀ k, Integrable (fun x ↦ f x^2) (P k : Measure X))
    (hb : ∀ k, (∫ x, f x^2 ∂(P k : Measure X)) ≤ C) :
    Tendsto (fun k ↦ ∫ x, f x ∂(P k : Measure X)) atTop
      (𝓝 (∫ x, f x ∂(Q : Measure X))) := by
  obtain ⟨hQi, hQb⟩ := square_bound P Q hlim f hf C hi hb
  have hC : 0 ≤ C := (integral_nonneg fun x ↦ sq_nonneg (f x)).trans (hb 0)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let R : ℝ := 1+6*C/ε
  have hR : 0 < R := by dsimp [R]; positivity
  have hsmall : C/R < ε/3 := by
    rw [div_lt_iff₀ hR]
    dsimp [R]
    field_simp
    nlinarith
  have hw := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim (clip f hf R hR.le)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hw (ε/3) (by positivity)
  refine ⟨N, fun k hk ↦ ?_⟩
  have h1 := integral_clip_error (P k : Measure X) f hf (hi k) C R (hb k) hR
  have h2 := integral_clip_error (Q : Measure X) f hf hQi C R hQb hR
  have h3 := hN k hk
  have ht := dist_triangle (∫ x, f x ∂(P k : Measure X))
    (∫ x, clip f hf R hR.le x ∂(P k : Measure X)) (∫ x, f x ∂(Q : Measure X))
  have ht' := dist_triangle (∫ x, clip f hf R hR.le x ∂(P k : Measure X))
    (∫ x, clip f hf R hR.le x ∂(Q : Measure X)) (∫ x, f x ∂(Q : Measure X))
  rw [dist_comm (∫ x, clip f hf R hR.le x ∂(Q : Measure X))
    (∫ x, f x ∂(Q : Measure X))] at ht'
  simp only [dist_eq_norm] at ht ht' h3 ⊢
  nlinarith

/-- Exact zero identities with uniformly converging compensators give
asymptotically zero identities for the limiting compensator. The test
itself may be unbounded; its actual integrability is retained. -/
theorem integrals_tendsto_zero_of_uniform_error (f : X → ℝ) (fn : ℕ → X → ℝ)
    (hf : ∀ k, Integrable f (P k : Measure X))
    (hfn : ∀ k, Integrable (fn k) (P k : Measure X))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ k x, ‖f x-fn k x‖ ≤ ε k)
    (hzero : ∀ k, (∫ x, fn k x ∂(P k : Measure X)) = 0) :
    Tendsto (fun k ↦ ∫ x, f x ∂(P k : Measure X)) atTop (𝓝 0) := by
  have hb (k : ℕ) : ‖∫ x, f x ∂(P k : Measure X)‖ ≤ ε k := by
    have he := norm_integral_le_of_norm_le_const
      (μ := (P k : Measure X)) (Filter.Eventually.of_forall (hbound k))
    rw [integral_sub (hf k) (hfn k), hzero k, sub_zero, probReal_univ, mul_one] at he
    exact he
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero (fun k ↦ norm_nonneg _) hb hε)

end SHEStochastic.WeakLimitMomentTests
