module

public import MathFin.Foundations.ItoIntegralL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.L2ProductLimit
open MeasureTheory Filter
open scoped ENNReal Topology

/-- Mean-square convergence implies convergence of every fixed L2
pairing. This is continuity of the existing Hilbert inner product. -/
theorem integral_mul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ)
    (X : ℕ → Ω → ℝ) (hX : ∀ n, MemLp (X n) 2 μ)
    (hlim : Tendsto (fun n ↦ ∫ sample, X n sample^2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ sample, f sample*X n sample ∂μ) atTop (𝓝 0) := by
  let b : Lp ℝ 2 μ := hf.toLp f
  let V (n : ℕ) : Lp ℝ 2 μ := (hX n).toLp (X n)
  have hn (n : ℕ) : ‖V n‖^2 = ∫ sample, X n sample^2 ∂μ :=
    (MathFin.ItoIntegralL2.lp_two_norm_sq (V n)).trans
      (integral_congr_ae ((hX n).coeFn_toLp.pow_const 2))
  have he (n : ℕ) : Real.sqrt (∫ sample, X n sample^2 ∂μ) = ‖V n‖ := by
    rw [← hn, Real.sqrt_sq (norm_nonneg _)]
  have hvn : Tendsto (fun n ↦ ‖V n‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, he, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hlim
  have hv : Tendsto V atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hvn
  have hp (n : ℕ) : innerSL ℝ b (V n) = ∫ sample, f sample*X n sample ∂μ := by
    rw [innerSL_apply_apply, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, (hX n).coeFn_toLp] with sample hf hX
    rw [hf, hX]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  simpa only [Function.comp_def, hp, map_zero] using ((innerSL ℝ b).continuous.tendsto (0 : Lp ℝ 2 μ)).comp hv

end SHEStochastic.L2ProductLimit
