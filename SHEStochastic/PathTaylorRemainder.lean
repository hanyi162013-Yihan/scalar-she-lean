module

public import SHEStochastic.SecondOrderTaylor
public import MathFin.Foundations.ItoFormulaAdapted
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Module.Convex

/-! The partition and compactness proof follows the public scalar
ItoFormulaAdapted.tendsto_sum_discreteTaylorRemainder. The Hessian here
is a bilinear operator on an arbitrary finite-dimensional state, and
may also vary continuously with time. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.PathTaylorRemainder
open Set Filter SHE.GaussianTaylor MathFin.QuadraticVariationL2
open scoped NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Uniformly small mesh gives uniformly small increments of every
continuous normed-space path. -/
theorem eventually_norm_increment_lt (H : ℝ≥0) {x : ℝ≥0 → E}
    (hx : ContinuousOn x (Icc 0 H)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k < n,
      ‖x (unifPart H n (k + 1)) - x (unifPart H n k)‖ < ε := by
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hx) ε hε
  filter_upwards [(tendsto_const_div_atTop_nhds_zero_nat (H : ℝ)).eventually_lt_const hδ]
    with n hn k hk
  rw [← dist_eq_norm]
  refine h _ ⟨zero_le, MathFin.ItoIntegralBrownian.unifPart_le_T (Nat.succ_le_of_lt hk)⟩
    _ ⟨zero_le, MathFin.ItoIntegralBrownian.unifPart_le_T hk.le⟩ ?_
  rwa [NNReal.dist_eq, MathFin.AdaptedQuadraticVariation.unifPart_succ_sub,
    abs_of_nonneg (by positivity)]

variable [ProperSpace E]

/-- Along a continuous path, all finite-dimensional C² Taylor
remainders vanish on any refining subsequence whose quadratic sums stay
bounded. Only continuity of the time-dependent Hessian is needed. -/
theorem tendsto (H : ℝ≥0) (G : ℝ≥0 → E → ℝ)
    (hG : ∀ t, ContDiff ℝ 2 (G t))
    (hH : Continuous (fun p : ℝ≥0 × E ↦ hessian (G p.1) p.2))
    {x : ℝ≥0 → E} (hx : ContinuousOn x (Icc 0 H)) {ν : ℕ → ℕ}
    (hν : Tendsto ν atTop atTop) {Q : ℝ}
    (hQ : ∀ᶠ i in atTop, ∑ k ∈ Finset.range (ν i),
      ‖x (unifPart H (ν i) (k + 1)) - x (unifPart H (ν i) k)‖ ^ 2 ≤ Q) :
    Tendsto (fun i ↦ ∑ k ∈ Finset.range (ν i), SecondOrderTaylor.remainder (G (unifPart H (ν i) k))
      (x (unifPart H (ν i) k)) (x (unifPart H (ν i) (k + 1)))) atTop (𝓝 0) := by
  letI : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
  letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hx
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  have hη : 0 < ε / (|Q| + 1) := by positivity
  have hK : IsCompact (Icc (0 : ℝ≥0) H ×ˢ Metric.closedBall (0 : E) R) :=
    isCompact_Icc.prod (isCompact_closedBall 0 R)
  have hHu : UniformContinuousOn (fun p : ℝ≥0 × E ↦ hessian (G p.1) p.2)
      (Icc (0 : ℝ≥0) H ×ˢ Metric.closedBall (0 : E) R) :=
    hK.uniformContinuousOn_of_continuous hH.continuousOn
  obtain ⟨δ, hδ, hδH⟩ := (Metric.uniformContinuousOn_iff (f := fun p : ℝ≥0 × E ↦ hessian (G p.1) p.2)).1 hHu _ hη
  filter_upwards [hν.eventually (eventually_norm_increment_lt H hx hδ), hQ] with i hosc hQi
  have hmem {k : ℕ} (hk : k ≤ ν i) : x (unifPart H (ν i) k) ∈ Metric.closedBall (0 : E) R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      hR _ ⟨zero_le, MathFin.ItoIntegralBrownian.unifPart_le_T hk⟩
  have hrem (k : ℕ) (hk : k < ν i) :
      ‖SecondOrderTaylor.remainder (G (unifPart H (ν i) k))
        (x (unifPart H (ν i) k)) (x (unifPart H (ν i) (k + 1)))‖ ≤
        ε / (|Q| + 1) * ‖x (unifPart H (ν i) (k + 1)) - x (unifPart H (ν i) k)‖ ^ 2 := by
    apply SecondOrderTaylor.remainder_bound (hG _) _ _ _ hη.le
    intro t ht
    let t₀ := unifPart H (ν i) k
    let x₀ := x t₀
    let x₁ := x (unifPart H (ν i) (k + 1))
    have ht₀ : t₀ ∈ Icc (0 : ℝ≥0) H :=
      ⟨zero_le, MathFin.ItoIntegralBrownian.unifPart_le_T hk.le⟩
    have hsegment : x₀ + t • (x₁ - x₀) ∈ Metric.closedBall (0 : E) R :=
      (convex_closedBall (0 : E) R).add_smul_sub_mem (hmem hk.le) (hmem (Nat.succ_le_of_lt hk)) ht
    have hd : dist (t₀, x₀ + t • (x₁ - x₀)) (t₀, x₀) < δ := by
      simp only [Prod.dist_eq, dist_self, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg ht.1, max_eq_right (mul_nonneg ht.1 (norm_nonneg _))]
      exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans_lt (hosc k hk)
    have hh := hδH (t₀, x₀ + t • (x₁ - x₀)) ⟨ht₀, hsegment⟩ (t₀, x₀) ⟨ht₀, hmem hk.le⟩ hd
    rw [dist_eq_norm (hessian (G t₀) (x₀ + t • (x₁ - x₀))) (hessian (G t₀) x₀)] at hh
    exact hh.le
  rw [dist_eq_norm, sub_zero]
  calc
    _ ≤ ∑ k ∈ Finset.range (ν i), ε / (|Q| + 1) *
        ‖x (unifPart H (ν i) (k + 1)) - x (unifPart H (ν i) k)‖ ^ 2 :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk ↦ hrem k (Finset.mem_range.mp hk))
    _ = ε / (|Q| + 1) * ∑ k ∈ Finset.range (ν i),
        ‖x (unifPart H (ν i) (k + 1)) - x (unifPart H (ν i) k)‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ ε / (|Q| + 1) * |Q| := by gcongr; exact hQi.trans (le_abs_self Q)
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg Q]

end SHEStochastic.PathTaylorRemainder
