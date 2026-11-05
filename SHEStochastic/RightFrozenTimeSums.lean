module

public import SHEStochastic.WeightedPrimitiveSums
public import MathFin.Foundations.AdaptedQuadraticVariation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section

namespace SHEStochastic.RightFrozenTimeSums
open MeasureTheory Filter Set MathFin.QuadraticVariationL2
open scoped NNReal Topology

/-- The right endpoint of the containing cell converges to the sampled
time, just as the public left-endpoint construction does. -/
theorem tendsto_right (H : ℝ≥0) {s : ℝ≥0} (hs : s ∈ Ioc 0 H) {g : ℝ≥0 → ℝ}
    (hg : ContinuousWithinAt g (Icc 0 H) s) :
    Tendsto (fun n ↦ ∑ k ∈ Finset.range n,
      (Ioc (unifPart H n k) (unifPart H n (k + 1))).indicator
        (fun _ ↦ g (unifPart H n (k + 1))) s) atTop (𝓝 (g s)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.mp hg ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (H : ℝ) / δ)
  refine ⟨max N 1, fun n hn ↦ ?_⟩
  have hn1 : 0 < n := one_pos.trans_le ((le_max_right _ _).trans hn)
  obtain ⟨k, hk, he, hclose⟩ := MathFin.ItoIntegralRiemannBridge.cell_collapse H n hn1 s hs
    (fun j ↦ g (unifPart H n (j + 1)))
  rw [he]
  apply hδc ⟨zero_le, MathFin.ItoIntegralBrownian.unifPart_le_T (Nat.succ_le_of_lt hk)⟩
  rw [NNReal.dist_eq]
  have hdist : |(unifPart H n (k + 1) : ℝ) - s| ≤ 2 * (H : ℝ) / n := by
    have ht := abs_sub_le (unifPart H n (k + 1) : ℝ) (unifPart H n k) s
    rw [MathFin.AdaptedQuadraticVariation.unifPart_succ_sub,
      abs_of_nonneg (div_nonneg H.coe_nonneg (Nat.cast_nonneg n))] at ht
    calc
      _ ≤ (H : ℝ) / n + |(unifPart H n k : ℝ) - s| := ht
      _ ≤ (H : ℝ) / n + (H : ℝ) / n := add_le_add_right hclose _
      _ = _ := by ring
  refine hdist.trans_lt ?_
  rw [div_lt_iff₀ (Nat.cast_pos.2 hn1), mul_comm]
  nlinarith [(div_lt_iff₀ hδ).mp (hN.trans_le (Nat.cast_le.2 ((le_max_left _ _).trans hn)))]

variable {E : Type*} [TopologicalSpace E]

def step (H : ℝ≥0) (q : ℝ≥0 → E → ℝ) (x : ℝ≥0 → E) (n : ℕ) (r : ℝ≥0) : ℝ :=
  ∑ k ∈ Finset.range n,
    (Ioc (unifPart H n k) (unifPart H n (k + 1))).indicator
      (fun r ↦ q r (x (unifPart H n (k + 1)))) r

/-- Freezing the state at right endpoints is compatible with an
integrable time envelope and mere statewise continuity of the time
derivative. No time continuity of that derivative is assumed. -/
theorem tendsto_integral (H : ℝ≥0) (q : ℝ≥0 → E → ℝ) (x : ℝ≥0 → E)
    (hx : ContinuousOn x (Icc 0 H))
    (hm : ∀ z, Measurable (fun r ↦ q r z))
    (hc : ∀ r, Continuous (q r)) (v : ℝ≥0 → ℝ)
    (hv : Integrable v (MathFin.ItoIntegralCLM.timeMeasure_T H))
    (hqb : ∀ r ∈ Ioc 0 H, ∀ z, |q r z| ≤ v r) :
    Tendsto (fun n ↦ ∫ r, step H q x n r ∂MathFin.ItoIntegralCLM.timeMeasure_T H) atTop
      (𝓝 (∫ r, q r (x r) ∂MathFin.ItoIntegralCLM.timeMeasure_T H)) := by
  have hs : ∀ᵐ r ∂MathFin.ItoIntegralCLM.timeMeasure_T H, r ∈ Ioc 0 H :=
    ae_restrict_mem measurableSet_Ioc
  have hdom (n : ℕ) : ∀ᵐ r ∂MathFin.ItoIntegralCLM.timeMeasure_T H, ‖step H q x n r‖ ≤ v r := by
    filter_upwards [hs] with r hr
    have hv0 : 0 ≤ v r := (abs_nonneg (q r (x r))).trans (hqb r hr (x r))
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa [step] using hv0
    · obtain ⟨k, hk, he, hclose⟩ := MathFin.ItoIntegralRiemannBridge.cell_collapse H n hn r hr
        (fun j ↦ q r (x (unifPart H n (j + 1))))
      change ‖∑ k ∈ Finset.range n, (Ioc (unifPart H n k) (unifPart H n (k + 1))).indicator
        (fun _ ↦ q r (x (unifPart H n (k + 1)))) r‖ ≤ _
      rw [he, Real.norm_eq_abs]
      exact hqb r hr _
  have hpt : ∀ᵐ r ∂MathFin.ItoIntegralCLM.timeMeasure_T H,
      Tendsto (fun n ↦ step H q x n r) atTop (𝓝 (q r (x r))) := by
    filter_upwards [hs] with r hr
    exact tendsto_right H hr ((hc r).continuousAt.comp_continuousWithinAt (hx r ⟨zero_le, hr.2⟩))
  apply tendsto_integral_of_dominated_convergence v
  · intro n
    exact (Finset.stronglyMeasurable_fun_sum _ (fun k hk ↦
      (hm _).stronglyMeasurable.indicator measurableSet_Ioc)).aestronglyMeasurable
  · exact hv
  · exact hdom
  · exact hpt

theorem integrable_section (H : ℝ≥0) (q : ℝ≥0 → E → ℝ)
    (hm : ∀ z, Measurable (fun r ↦ q r z)) (v : ℝ≥0 → ℝ)
    (hv : Integrable v (MathFin.ItoIntegralCLM.timeMeasure_T H))
    (hqb : ∀ r ∈ Ioc 0 H, ∀ z, |q r z| ≤ v r) (z : E) :
    Integrable (fun r ↦ q r z) (MathFin.ItoIntegralCLM.timeMeasure_T H) := by
  apply hv.mono' (hm z).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := MathFin.ItoIntegralL2.timeMeasure)
    (measurableSet_Ioc (a := 0) (b := H))] with r hr
  simpa only [Real.norm_eq_abs] using hqb r hr z

/-- The time contribution obtained by freezing the state at each right
endpoint converges to the ordinary time integral. Its sole primitive
hypothesis will be supplied by the absolute-continuity FTC. -/
theorem tendsto_increments (H : ℝ≥0) (G q : ℝ≥0 → E → ℝ) (x : ℝ≥0 → E)
    (hx : ContinuousOn x (Icc 0 H)) (hm : ∀ z, Measurable (fun r ↦ q r z))
    (hc : ∀ r, Continuous (q r)) (v : ℝ≥0 → ℝ)
    (hv : Integrable v (MathFin.ItoIntegralCLM.timeMeasure_T H))
    (hqb : ∀ r ∈ Ioc 0 H, ∀ z, |q r z| ≤ v r)
    (hprimitive : ∀ s t : ℝ≥0, s ≤ t → t ≤ H → ∀ z,
      G t z - G s z = ∫ r, (Ioc s t).indicator (fun r ↦ q r z) r
        ∂MathFin.ItoIntegralCLM.timeMeasure_T H) :
    Tendsto (fun n ↦ ∑ k ∈ Finset.range n,
      (G (unifPart H n (k + 1)) (x (unifPart H n (k + 1))) -
        G (unifPart H n k) (x (unifPart H n (k + 1))))) atTop
      (𝓝 (∫ r, q r (x r) ∂MathFin.ItoIntegralCLM.timeMeasure_T H)) := by
  have he (n : ℕ) : (∑ k ∈ Finset.range n,
      (G (unifPart H n (k + 1)) (x (unifPart H n (k + 1))) -
        G (unifPart H n k) (x (unifPart H n (k + 1))))) =
      ∫ r, step H q x n r ∂MathFin.ItoIntegralCLM.timeMeasure_T H := by
    simp only [step]
    rw [integral_finsetSum _ (fun k hk ↦
      (integrable_section H q hm v hv hqb _).indicator measurableSet_Ioc)]
    exact Finset.sum_congr rfl (fun k hk ↦ hprimitive _ _
      (MathFin.ItoIntegralBrownian.unifPart_mono H n (Nat.le_succ k))
      (MathFin.ItoIntegralBrownian.unifPart_le_T (Nat.succ_le_of_lt (Finset.mem_range.mp hk))) _)
  simp_rw [he]
  exact tendsto_integral H q x hx hm hc v hv hqb

end SHEStochastic.RightFrozenTimeSums
