module

public import SHEStochastic.WeakLimitMomentMartingale
public import SHEStochastic.QuadraticMomentBounds
public import SHEStochastic.SubGaussianFourthMoment

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.WeakLimitCompensatedProducts
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

variable {X Y T : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
  [MeasurableSpace X] [BorelSpace X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [Preorder T]

def value (M N : T → X → ℝ) (A : T → BoundedContinuousFunction X ℝ) (t : T) (x : X) : ℝ :=
  M t x*N t x-A t x

/-- Square and mixed compensator martingales pass to a weak joint
limit under uniform coefficient approximation. Existing fourth moments
control the unbounded products; only the compensators vary with k. -/
theorem martingale (P : ℕ → ProbabilityMeasure X) (Q : ProbabilityMeasure X)
    (hlim : Tendsto P atTop (𝓝 Q))
    (F : Filtration T ‹MeasurableSpace X›) (past : T → X → Y) (hpast : ∀ t, Continuous (past t))
    (hF : ∀ t, F t ≤ MeasurableSpace.comap (past t) inferInstance)
    (M N : T → X → ℝ) (hcM : ∀ t, Continuous (M t)) (hcN : ∀ t, Continuous (N t))
    (haM : StronglyAdapted F M) (haN : StronglyAdapted F N)
    (c d : T → ℝ≥0)
    (hM : ∀ k t, HasSubgaussianMGF (M t) (c t) (P k : Measure X))
    (hN : ∀ k t, HasSubgaussianMGF (N t) (d t) (P k : Measure X))
    (A : T → BoundedContinuousFunction X ℝ) (An : ℕ → T → BoundedContinuousFunction X ℝ)
    (hA : StronglyAdapted F (fun t x ↦ A t x))
    (hclose : ∀ t, Tendsto (fun k ↦ ‖A t-An k t‖) atTop (𝓝 0))
    (htest : ∀ k s t, s ≤ t → ∀ ψ : BoundedContinuousFunction Y ℝ,
      (∫ x, ψ (past s x)*(value M N (An k) t x-value M N (An k) s x) ∂(P k : Measure X)) = 0) :
    Martingale (value M N A) F (Q : Measure X) := by
  let Cm (t : T) := 48*Real.exp (1/2 : ℝ)*(c t : ℝ)^2
  let Cn (t : T) := 48*Real.exp (1/2 : ℝ)*(d t : ℝ)^2
  have hmom (k : ℕ) (t : T) (B : BoundedContinuousFunction X ℝ) :=
    QuadraticMomentBounds.product_sub_bounded (P k : Measure X)
      (show MemLp (M t) 4 (P k : Measure X) from by simpa using (hM k t).memLp (4 : ℝ≥0))
      (show MemLp (N t) 4 (P k : Measure X) from by simpa using (hN k t).memLp (4 : ℝ≥0))
      B.continuous.stronglyMeasurable.aestronglyMeasurable ‖B‖ (fun x ↦ B.norm_coe_le_norm x)
      (Cm t) (Cn t) (SubGaussianFourthMoment.integral_fourth_le (hM k t))
      (SubGaussianFourthMoment.integral_fourth_le (hN k t))
  apply WeakLimitMomentMartingale.of_tests_tendsto P Q hlim F past hpast hF (value M N A)
    (fun t ↦ ((hcM t).mul (hcN t)).sub (A t).continuous) ((haM.mul haN).sub hA)
    (fun t ↦ Cm t+Cn t+2*‖A t‖^2)
    (fun k t ↦ (hmom k t (A t)).1) (fun k t ↦ (hmom k t (A t)).2)
  intro s t hst ψ
  have hInt (k : ℕ) (B : T → BoundedContinuousFunction X ℝ) :
      Integrable (fun x ↦ ψ (past s x)*(value M N B t x-value M N B s x)) (P k : Measure X) := by
    have hψ : MemLp (fun x ↦ ψ (past s x)) ∞ (P k : Measure X) :=
      MemLp.of_bound (ψ.continuous.comp (hpast s)).stronglyMeasurable.aestronglyMeasurable
        ‖ψ‖ (Filter.Eventually.of_forall fun x ↦ ψ.norm_coe_le_norm _)
    exact (hψ.mul ((hmom k t (B t)).1.sub (hmom k s (B s)).1)).integrable one_le_two
  apply WeakLimitMomentTests.integrals_tendsto_zero_of_uniform_error P
    (fun x ↦ ψ (past s x)*(value M N A t x-value M N A s x))
    (fun k x ↦ ψ (past s x)*(value M N (An k) t x-value M N (An k) s x))
    (fun k ↦ hInt k A) (fun k ↦ hInt k (An k))
    (fun k ↦ ‖ψ‖*(‖A t-An k t‖+‖A s-An k s‖))
  · simpa only [add_zero, mul_zero] using tendsto_const_nhds.mul ((hclose t).add (hclose s))
  · intro k x
    have he : ψ (past s x)*(value M N A t x-value M N A s x) -
        ψ (past s x)*(value M N (An k) t x-value M N (An k) s x) =
        ψ (past s x)*((An k t x-A t x)-(An k s x-A s x)) := by unfold value; ring
    rw [he, norm_mul]
    have ht : ‖An k t x-A t x‖ ≤ ‖A t-An k t‖ := by
      rw [norm_sub_rev, ← BoundedContinuousFunction.sub_apply]
      exact (A t-An k t).norm_coe_le_norm x
    have hs : ‖An k s x-A s x‖ ≤ ‖A s-An k s‖ := by
      rw [norm_sub_rev, ← BoundedContinuousFunction.sub_apply]
      exact (A s-An k s).norm_coe_le_norm x
    exact mul_le_mul (ψ.norm_coe_le_norm _) ((norm_sub_le _ _).trans (add_le_add ht hs))
      (norm_nonneg _) (norm_nonneg _)
  · exact fun k ↦ htest k s t hst ψ

end SHEStochastic.WeakLimitCompensatedProducts
