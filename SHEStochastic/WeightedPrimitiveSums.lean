module

public import SHEStochastic.SimplePrimitivePairing
public import MathFin.Foundations.ItoIntegralRiemannBridge

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section

namespace SHEStochastic.WeightedPrimitiveSums
open MeasureTheory ProbabilityTheory MathFin.QuadraticVariationL2
open scoped NNReal ENNReal Topology

local notation "ν" H => MathFin.ItoIntegralCLM.timeMeasure_T H

def step (H : ℝ≥0) (w : ℝ≥0 → ℝ) (n : ℕ) (r : ℝ≥0) : ℝ :=
  ∑ k ∈ Finset.range n,
    (Set.Ioc (unifPart H n k) (unifPart H n (k + 1))).indicator (fun _ ↦ w (unifPart H n k)) r

def primitive (H : ℝ≥0) (q : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  ∫ r, (Set.Iio t).indicator q r ∂ν H

/-- Finite primitive increments paired with left weights are the ordinary
time integral of the left-step weights against the original density. -/
theorem sum_eq_integral (H : ℝ≥0) (q w : ℝ≥0 → ℝ) (hq : Integrable q (ν H)) (n : ℕ) :
    (∑ k ∈ Finset.range n, w (unifPart H n k) *
      (primitive H q (unifPart H n (k + 1)) - primitive H q (unifPart H n k))) =
        ∫ r, step H w n r * q r ∂ν H := by
  letI : NullSingletonClass MathFin.ItoIntegralL2.timeMeasure :=
    ⟨MathFin.ItoIntegralL2.timeMeasure_singleton⟩
  haveI : NullSingletonClass (ν H) := by dsimp [MathFin.ItoIntegralCLM.timeMeasure_T]; infer_instance
  have he : (fun r ↦ step H w n r * q r) = (fun r ↦ ∑ k ∈ Finset.range n,
      (Set.Ioc (unifPart H n k) (unifPart H n (k + 1))).indicator
        (fun r ↦ w (unifPart H n k) * q r) r) := by
    funext r
    simp only [step, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hr : r ∈ Set.Ioc (unifPart H n k) (unifPart H n (k + 1)) <;>
      simp [Set.indicator_apply, hr]
  rw [he, integral_finsetSum _ (fun k hk ↦
    (hq.const_mul (w (unifPart H n k))).indicator measurableSet_Ioc)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [primitive, primitive, SimplePrimitivePairing.primitive_sub (ν H) q hq _ _
    (MathFin.ItoIntegralBrownian.unifPart_mono H n (Nat.le_succ k)),
    integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc, integral_const_mul]

/-- Continuous bounded weights may be integrated against any L¹ time
density. No continuity or boundedness of that density is required. -/
theorem tendsto (H : ℝ≥0) (q w : ℝ≥0 → ℝ) (hq : Integrable q (ν H))
    (hw : ContinuousOn w (Set.Icc 0 H)) (B : ℝ) (hB : 0 ≤ B) (hwb : ∀ t, |w t| ≤ B) :
    Filter.Tendsto (fun n ↦ ∑ k ∈ Finset.range n, w (unifPart H n k) *
      (primitive H q (unifPart H n (k + 1)) - primitive H q (unifPart H n k)))
      Filter.atTop (𝓝 (∫ r, w r * q r ∂ν H)) := by
  have hsupp : ∀ᵐ r ∂ν H, r ∈ Set.Ioc 0 H := ae_restrict_mem measurableSet_Ioc
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun r ↦ step H w n r * q r) (ν H) := by
    have hm : StronglyMeasurable (step H w n) :=
      Finset.stronglyMeasurable_fun_sum _ (fun k hk ↦ stronglyMeasurable_const.indicator measurableSet_Ioc)
    exact hm.aestronglyMeasurable.mul hq.aestronglyMeasurable
  have hdom (n : ℕ) : ∀ᵐ r ∂ν H, ‖step H w n r * q r‖ ≤ B * |q r| := by
    filter_upwards [hsupp] with r hr
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right
      (MathFin.ItoIntegralRiemannBridge.abs_sum_indicator_unifPart_le H n hr hB hwb) (abs_nonneg _)
  have hpt : ∀ᵐ r ∂ν H, Filter.Tendsto (fun n ↦ step H w n r * q r) Filter.atTop (𝓝 (w r * q r)) := by
    filter_upwards [hsupp] with r hr
    exact (MathFin.ItoIntegralRiemannBridge.tendsto_sum_indicator_unifPart H hr
      (hw r ⟨zero_le, hr.2⟩)).mul_const (q r)
  have ht := tendsto_integral_of_dominated_convergence (fun r ↦ B * |q r|) hmeas
    (hq.abs.const_mul B) hdom hpt
  simpa only [← sum_eq_integral H q w hq] using ht

end SHEStochastic.WeightedPrimitiveSums
