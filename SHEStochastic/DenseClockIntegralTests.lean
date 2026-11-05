module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Instances.NNReal.Lemmas

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.DenseClockIntegralTests
open MeasureTheory Filter
open scoped NNReal Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure Ω) (M : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (M t))
  (hc : ∀ sample, Continuous (fun t ↦ M t sample))
  (past : ℝ≥0 → Ω → X) (hpm : ∀ t, Measurable (past t))
  (hpc : ∀ sample, Continuous (fun t ↦ past t sample))
  (D : Ω → ℝ) (hD : Integrable D μ) (hbound : ∀ t sample, ‖M t sample‖ ≤ D sample)

include hm hc hpm hpc hD hbound in
theorem integral_tendsto (s t : ℝ≥0) (sn tn : ℕ → ℝ≥0)
    (hs : Tendsto sn atTop (𝓝 s)) (ht : Tendsto tn atTop (𝓝 t))
    (ψ : BoundedContinuousFunction X ℝ) :
    Tendsto (fun n ↦ ∫ sample, ψ (past (sn n) sample)*(M (tn n) sample-M (sn n) sample) ∂μ)
      atTop (𝓝 (∫ sample, ψ (past s sample)*(M t sample-M s sample) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun sample ↦ 2*‖ψ‖*D sample)
  · intro n
    exact ((ψ.continuous.measurable.comp (hpm (sn n))).mul
      ((hm (tn n)).sub (hm (sn n)))).stronglyMeasurable.aestronglyMeasurable
  · exact hD.const_mul _
  · intro n
    exact Filter.Eventually.of_forall fun sample ↦ by
      calc
        _ = ‖ψ (past (sn n) sample)‖*‖M (tn n) sample-M (sn n) sample‖ := norm_mul _ _
        _ ≤ ‖ψ‖*(‖M (tn n) sample‖+‖M (sn n) sample‖) :=
          mul_le_mul (ψ.norm_coe_le_norm _) (norm_sub_le _ _) (norm_nonneg _) (norm_nonneg _)
        _ ≤ ‖ψ‖*(D sample+D sample) :=
          mul_le_mul_of_nonneg_left (add_le_add (hbound _ _) (hbound _ _)) (norm_nonneg _)
        _ = _ := by ring
  · exact Filter.Eventually.of_forall fun sample ↦
      ((ψ.continuous.tendsto _).comp ((hpc sample).tendsto _ |>.comp hs)).mul
        (((hc sample).tendsto _ |>.comp ht).sub ((hc sample).tendsto _ |>.comp hs))

include hm hc hpm hpc hD hbound in
/-- Continuity and one integrable path bound extend past-test identities
from any dense countable collection to every real nonnegative clock. -/
theorem zero_of_dense (r : ℕ → ℝ≥0) (hdense : DenseRange r)
    (hzero : ∀ i j, r i ≤ r j → ∀ ψ : BoundedContinuousFunction X ℝ,
      (∫ sample, ψ (past (r i) sample)*(M (r j) sample-M (r i) sample) ∂μ) = 0)
    (s t : ℝ≥0) (hst : s ≤ t) (ψ : BoundedContinuousFunction X ℝ) :
    (∫ sample, ψ (past s sample)*(M t sample-M s sample) ∂μ) = 0 := by
  by_cases heq : s = t
  · subst t
    simp
  have hseq (u : ℝ≥0) : ∃ i : ℕ → ℕ, Tendsto (fun n ↦ r (i n)) atTop (𝓝 u) := by
    obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp (hdense u)
    choose i hi using hv
    refine ⟨i, ?_⟩
    have he : (fun n ↦ r (i n)) = v := funext hi
    rw [he]
    exact hlim
  obtain ⟨i, hi⟩ := hseq s
  obtain ⟨j, hj⟩ := hseq t
  have hl := integral_tendsto μ M hm hc past hpm hpc D hD hbound s t _ _ hi hj ψ
  have he : ∀ᶠ n in atTop,
      (∫ sample, ψ (past (r (i n)) sample)*(M (r (j n)) sample-M (r (i n)) sample) ∂μ) = 0 :=
    (hi.eventually_lt hj (lt_of_le_of_ne hst heq)).mono fun n hn ↦ hzero (i n) (j n) hn.le ψ
  exact tendsto_nhds_unique hl (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he))

end SHEStochastic.DenseClockIntegralTests
