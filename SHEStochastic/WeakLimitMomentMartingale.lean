module

public import SHEStochastic.WeakLimitMomentTests
public import SHEStochastic.BCFPastTesting
public import SHEStochastic.ContinuousStoppedMartingaleTests

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.WeakLimitMomentMartingale
open MeasureTheory Filter
open scoped Topology ENNReal

variable {X Y T : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
  [MeasurableSpace X] [BorelSpace X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [Preorder T]
  (P : ℕ → ProbabilityMeasure X) (Q : ProbabilityMeasure X)
  (hlim : Tendsto P atTop (𝓝 Q))
  (F : Filtration T ‹MeasurableSpace X›) (past : T → X → Y) (hpast : ∀ t, Continuous (past t))
  (hF : ∀ t, F t ≤ MeasurableSpace.comap (past t) inferInstance)
  (M : T → X → ℝ) (hc : ∀ t, Continuous (M t)) (ha : StronglyAdapted F M)
  (C : T → ℝ) (hM : ∀ k t, MemLp (M t) 2 (P k : Measure X))
  (hbound : ∀ k t, (∫ x, M t x^2 ∂(P k : Measure X)) ≤ C t)

include hbound hpast hM in
theorem weighted_bound (k : ℕ) (s t : T) (ψ : BoundedContinuousFunction Y ℝ) :
    (∫ x, (ψ (past s x)*(M t x-M s x))^2 ∂(P k : Measure X)) ≤
      2*‖ψ‖^2*(C t+C s) := by
  have hψ : MemLp (fun x ↦ ψ (past s x)) ∞ (P k : Measure X) :=
    MemLp.of_bound (ψ.continuous.comp (hpast s)).stronglyMeasurable.aestronglyMeasurable
      ‖ψ‖ (Filter.Eventually.of_forall fun x ↦ ψ.norm_coe_le_norm _)
  have hi := (hψ.mul ((hM k t).sub (hM k s))).integrable_sq
  have hd := ((hM k t).integrable_sq.add (hM k s).integrable_sq).const_mul (2*‖ψ‖^2)
  calc
    _ ≤ ∫ x, (2*‖ψ‖^2)*(M t x^2+M s x^2) ∂(P k : Measure X) := by
      apply integral_mono hi hd
      intro x
      have hψb : (ψ (past s x))^2 ≤ ‖ψ‖^2 := by
        simpa only [Real.norm_eq_abs, sq_abs] using
          pow_le_pow_left₀ (norm_nonneg _) (ψ.norm_coe_le_norm (past s x)) 2
      calc
        _ = (ψ (past s x))^2*(M t x-M s x)^2 := mul_pow _ _ _
        _ ≤ ‖ψ‖^2*(2*(M t x^2+M s x^2)) :=
          mul_le_mul hψb (by nlinarith [sq_nonneg (M t x+M s x)])
            (sq_nonneg _) (sq_nonneg _)
        _ = _ := by simp only [Pi.add_apply]; ring
    _ = (2*‖ψ‖^2)*((∫ x, M t x^2 ∂(P k : Measure X))+
        (∫ x, M s x^2 ∂(P k : Measure X))) := by
      rw [integral_const_mul, integral_add (hM k t).integrable_sq (hM k s).integrable_sq]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add (hbound k t) (hbound k s)) (by positivity)

include hlim hbound hF ha hpast hM hc in
/-- Uniform second moments preserve ordinary martingales under weak
joint path limits. Quadratic and mixed compensated processes are
covered by applying the same result with their fourth-moment bounds. -/
theorem of_tests_tendsto
    (htest : ∀ s t, s ≤ t → ∀ ψ : BoundedContinuousFunction Y ℝ,
      Tendsto (fun k ↦ ∫ x, ψ (past s x)*(M t x-M s x) ∂(P k : Measure X)) atTop (𝓝 0)) :
    Martingale M F (Q : Measure X) := by
  have hQ (t : T) : MemLp (M t) 2 (Q : Measure X) :=
    (memLp_two_iff_integrable_sq (hc t).stronglyMeasurable.aestronglyMeasurable).mpr
      (WeakLimitMomentTests.square_bound P Q hlim (M t) (hc t) (C t)
        (fun k ↦ (hM k t).integrable_sq) (fun k ↦ hbound k t)).1
  apply BCFPastTesting.martingale (Q : Measure X) F past (fun t ↦ (hpast t).measurable) hF M ha hQ
  intro s t hst ψ
  have hψ (k : ℕ) : MemLp (fun x ↦ ψ (past s x)) ∞ (P k : Measure X) :=
    MemLp.of_bound (ψ.continuous.comp (hpast s)).stronglyMeasurable.aestronglyMeasurable
      ‖ψ‖ (Filter.Eventually.of_forall fun x ↦ ψ.norm_coe_le_norm _)
  have hl := WeakLimitMomentTests.integral_tendsto P Q hlim
    (fun x ↦ ψ (past s x)*(M t x-M s x))
    ((ψ.continuous.comp (hpast s)).mul ((hc t).sub (hc s)))
    (2*‖ψ‖^2*(C t+C s))
    (fun k ↦ ((hψ k).mul ((hM k t).sub (hM k s))).integrable_sq)
    (fun k ↦ weighted_bound P past hpast M C hM hbound k s t ψ)
  exact tendsto_nhds_unique hl (htest s t hst ψ)

include hlim hbound hF ha hpast hM hc in
theorem martingale
    (htest : ∀ k s t, s ≤ t → ∀ ψ : BoundedContinuousFunction Y ℝ,
      (∫ x, ψ (past s x)*(M t x-M s x) ∂(P k : Measure X)) = 0) :
    Martingale M F (Q : Measure X) :=
  of_tests_tendsto P Q hlim F past hpast hF M hc ha C hM hbound
    (fun s t hst ψ ↦ (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0)).congr
      (fun k ↦ (htest k s t hst ψ).symm))

end SHEStochastic.WeakLimitMomentMartingale
