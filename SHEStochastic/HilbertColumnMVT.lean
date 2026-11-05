module

public import SHE.HilbertColumns
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Normed.Lp.PiLp

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.HilbertColumnMVT
variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Uniform square-summable derivative energy on a segment controls
the full countable signed column difference. Only finite-dimensional
mean value calculus is needed, so no differentiability of an infinite
column-valued map is assumed. -/
theorem energy (F A : I → ℝ → E) (C : ℝ) (hC : 0 ≤ C)
    (hD : ∀ i s, s ∈ Set.Icc (0 : ℝ) 1 → HasDerivAt (F i) (A i s) s)
    (hS : ∀ s, s ∈ Set.Icc (0 : ℝ) 1 → Summable (fun i => ‖A i s‖^2))
    (hA : ∀ s, s ∈ Set.Icc (0 : ℝ) 1 → (∑' i, ‖A i s‖^2) ≤ C) :
    Summable (fun i => ‖F i 1 - F i 0‖^2) ∧ (∑' i, ‖F i 1 - F i 0‖^2) ≤ C := by
  classical
  have hfinite (a : Finset I) : (∑ i ∈ a, ‖F i 1 - F i 0‖^2) ≤ C := by
    let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : a => E)).symm.toContinuousLinearMap
    let f := fun s : ℝ => L (fun i : a => F i s)
    let df := fun s : ℝ => L (fun i : a => A i s)
    have hd (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) : HasDerivAt f (df s) s :=
      L.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_pi.mpr (fun i => hD i s hs))
    have hb (s : ℝ) (hs : s ∈ Set.Ico (0 : ℝ) 1) : ‖df s‖ ≤ Real.sqrt C := by
      have hs' : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
      apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg C)).mp
      rw [Real.sq_sqrt hC, PiLp.norm_sq_eq_of_L2]
      change (∑ i : a, ‖A i s‖^2) ≤ C
      rw [Finset.sum_coe_sort a (fun i => ‖A i s‖^2)]
      exact ((hS s hs').sum_le_tsum a (fun i hi => sq_nonneg _)).trans (hA s hs')
    have hm := norm_image_sub_le_of_norm_deriv_le_segment_01'
      (fun s hs => (hd s hs).hasDerivWithinAt) hb
    have hq := pow_le_pow_left₀ (norm_nonneg _) hm 2
    rw [Real.sq_sqrt hC] at hq
    convert! hq using 1
    rw [PiLp.norm_sq_eq_of_L2]
    change (∑ i ∈ a, ‖F i 1 - F i 0‖^2) = ∑ i : a, ‖F i 1 - F i 0‖^2
    exact (Finset.sum_coe_sort a _).symm
  exact ⟨summable_of_sum_le (fun _ => sq_nonneg _) hfinite,
    Real.tsum_le_of_sum_le (fun _ => sq_nonneg _) hfinite⟩

end SHEStochastic.HilbertColumnMVT
