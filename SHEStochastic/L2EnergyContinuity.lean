module

public import SHEStochastic.HilbertSimpleInputs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.L2EnergyContinuity
open MeasureTheory
open scoped ENNReal Topology

variable {Ω C : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup C] [InnerProductSpace ℝ C]

theorem pointwise (x y : C) :
    |‖x‖ ^ 2 - ‖y‖ ^ 2| ≤ ‖x - y‖ * ‖x + y‖ := by
  have he : inner ℝ (x - y) (x + y) = ‖x‖ ^ 2 - ‖y‖ ^ 2 := by
    rw [inner_sub_left, inner_add_right, inner_add_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm y x]
    ring
  rw [← he]
  exact abs_real_inner_le_norm _ _

theorem norm_sq (u : Lp C 2 μ) : ∫ p, ‖u p‖ ^ 2 ∂μ = ‖u‖ ^ 2 := by
  calc
    _ = ∫ p, inner ℝ (u p) (u p) ∂μ := by simp only [real_inner_self_eq_norm_sq]
    _ = inner ℝ u u := (L2.inner_def _ _).symm
    _ = _ := real_inner_self_eq_norm_sq u

/-- Squared row norms vary continuously in L1 under L2 approximation.
The bound uses the original Hilbert-valued rows and no uniform bound. -/
theorem integral_sub_le (u v : Lp C 2 μ) :
    (∫ p, |‖u p‖ ^ 2 - ‖v p‖ ^ 2| ∂μ) ≤ ‖u - v‖ * (‖u‖ + ‖v‖) := by
  have hu := (Lp.memLp u).norm.integrable_sq
  have hv := (Lp.memLp v).norm.integrable_sq
  have hi := (Lp.memLp (u - v)).norm.integrable_mul (Lp.memLp (u + v)).norm
  have hc := integral_mul_norm_le_Lp_mul_Lq
    (f := fun p ↦ (u - v) p) (g := fun p ↦ (u + v) p) Real.HolderConjugate.two_two
    (by simpa only [ENNReal.ofReal_ofNat] using Lp.memLp (u - v))
    (by simpa only [ENNReal.ofReal_ofNat] using Lp.memLp (u + v))
  have hr (w : Lp C 2 μ) :
      (∫ p, ‖w p‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = ‖w‖ := by
    rw [show (fun p ↦ ‖w p‖ ^ (2 : ℝ)) = (fun p ↦ ‖w p‖ ^ (2 : ℕ)) from
      funext fun p ↦ Real.rpow_two _, ← Real.sqrt_eq_rpow, norm_sq,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [hr, hr] at hc
  calc
    _ ≤ ∫ p, ‖(u - v) p‖ * ‖(u + v) p‖ ∂μ := by
      apply integral_mono_ae (hu.sub hv).abs hi
      filter_upwards [Lp.coeFn_sub u v, Lp.coeFn_add u v] with p hs ha
      simp only [Pi.sub_apply, Pi.mul_apply]
      rw [hs, ha]
      exact pointwise _ _
    _ ≤ ‖u - v‖ * ‖u + v‖ := hc
    _ ≤ _ := mul_le_mul_of_nonneg_left (norm_add_le u v) (norm_nonneg _)

theorem tendsto_integral_sub {κ : Type*} {l : Filter κ} {u : κ → Lp C 2 μ} {v : Lp C 2 μ}
    (h : Filter.Tendsto u l (nhds v)) :
    Filter.Tendsto (fun k ↦ ∫ p, |‖u k p‖ ^ 2 - ‖v p‖ ^ 2| ∂μ) l (nhds 0) := by
  apply squeeze_zero (fun k ↦ integral_nonneg fun p ↦ abs_nonneg _)
    (fun k ↦ integral_sub_le (u k) v)
  have h1 : Filter.Tendsto (fun k ↦ ‖u k - v‖) l (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp h
  simpa using h1.mul (h.norm.add_const ‖v‖)

end SHEStochastic.L2EnergyContinuity
