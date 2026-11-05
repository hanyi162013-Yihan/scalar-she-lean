module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Order.Basic

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic.L1Approximation
open MeasureTheory Filter
open scoped Topology

/-- The ordinary L¹ triangle inequality, stated for representatives. -/
theorem triangle {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g h : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    (∫ ω, |f ω - h ω| ∂μ) ≤ (∫ ω, |f ω - g ω| ∂μ) + ∫ ω, |g ω - h ω| ∂μ := by
  have hi : (∫ ω, |f ω - g ω| ∂μ) + (∫ ω, |g ω - h ω| ∂μ) =
      ∫ ω, |(f - g) ω| + |(g - h) ω| ∂μ := by
    simpa only [Pi.sub_apply] using (integral_add (hf.sub hg).abs (hg.sub hh).abs).symm
  rw [hi]
  apply integral_mono (hf.sub hh).abs ((hf.sub hg).abs.add (hg.sub hh).abs)
  intro ω
  exact abs_sub_le (f ω) (g ω) (h ω)

/-- Uniform approximation errors tending to zero transfer a convergence
limit. The partition-size limit is taken after fixing the approximant. -/
theorem tendsto_zero {a e : ℕ → ℝ} {b : ℕ → ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (he : Tendsto e atTop (𝓝 0))
    (hb : ∀ k, Tendsto (b k) atTop (𝓝 0)) (hle : ∀ k n, a n ≤ e k + b k n) :
    Tendsto a atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro c hc
    exact Eventually.of_forall (fun n ↦ hc.trans_le (ha n))
  · intro c hc
    have hc2 : (0 : ℝ) < c / 2 := by linarith
    obtain ⟨k, hk⟩ := (he.eventually (gt_mem_nhds hc2)).exists
    filter_upwards [(hb k).eventually (gt_mem_nhds hc2)] with n hn
    linarith [hle k n]

end SHEStochastic.L1Approximation
