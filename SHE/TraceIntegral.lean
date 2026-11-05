module

public import SHE.HaarNegativeTrace
public import Mathlib.Analysis.Normed.Lp.PiLp

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.TraceIntegral
open Finset Set MeasureTheory
open scoped ENNReal

/-- The square trace of a genuine unit-interval integral is bounded
by any common square-trace bound of its integrand. Finite Hilbert
products prove the estimate before passing to the countable sum. -/
theorem square_trace {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → ι → E) (C : ℝ) (hC : 0 ≤ C)
    (hcont : ∀ i, ContinuousOn (fun r => F r i) (Icc (0:ℝ) 1))
    (hbound : ∀ r ∈ Icc (0:ℝ) 1, Summable (fun i => ‖F r i‖^2) ∧ (∑' i, ‖F r i‖^2) ≤ C) :
    Summable (fun i => ‖∫ r in (0:ℝ)..1,F r i‖^2) ∧
      (∑' i, ‖∫ r in (0:ℝ)..1,F r i‖^2) ≤ C := by
  classical
  have hfinite (s : Finset ι) : (∑ i ∈ s, ‖∫ r in (0:ℝ)..1,F r i‖^2) ≤ C := by
    let Φ : ℝ → PiLp 2 (fun _ : s => E) := fun r => WithLp.toLp 2 (fun i : s => F r i)
    have hΦ : ContinuousOn Φ (Icc (0:ℝ) 1) :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : s => E)).symm.continuous.comp_continuousOn
        (continuousOn_pi.mpr (fun i => hcont i))
    have hi := hΦ.intervalIntegrable_of_Icc (μ := volume) zero_le_one
    have hb : ∀ r ∈ uIoc (0:ℝ) 1, ‖Φ r‖ ≤ Real.sqrt C := by
      intro r hr
      have hr' : r ∈ Icc (0:ℝ) 1 := by
        rw [uIoc_of_le zero_le_one] at hr
        exact ⟨hr.1.le,hr.2⟩
      have hh := ((hbound r hr').1.sum_le_tsum s (fun i _ => sq_nonneg ‖F r i‖)).trans (hbound r hr').2
      have he : ‖Φ r‖^2 = ∑ i ∈ s, ‖F r i‖^2 := by
        rw [PiLp.norm_sq_eq_of_L2]
        exact Finset.sum_coe_sort s (fun i => ‖F r i‖^2)
      apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
      rw [Real.sq_sqrt hC,he]
      exact hh
    have hb' : ‖∫ r in (0:ℝ)..1, Φ r‖ ≤ Real.sqrt C := by
      simpa only [sub_zero,abs_one,mul_one] using intervalIntegral.norm_integral_le_of_norm_le_const hb
    have he : (∑ i ∈ s, ‖∫ r in (0:ℝ)..1,F r i‖^2) = ‖∫ r in (0:ℝ)..1,Φ r‖^2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      rw [← Finset.sum_coe_sort s (fun i => ‖∫ r in (0:ℝ)..1,F r i‖^2)]
      apply sum_congr rfl
      intro i _
      have hh := (PiLp.proj 2 (fun _ : s => E) (𝕜 := ℝ) i).intervalIntegral_comp_comm hi
      exact congrArg (fun z : E => ‖z‖^2) hh
    rw [he]
    exact (pow_le_pow_left₀ (norm_nonneg _) hb' 2).trans_eq (Real.sq_sqrt hC)
  exact ⟨summable_of_sum_le (fun _ => sq_nonneg _) hfinite,
    Real.tsum_le_of_sum_le (fun _ => sq_nonneg _) hfinite⟩

end SHE.TraceIntegral
