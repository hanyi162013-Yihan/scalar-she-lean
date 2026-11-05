module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic.SimpleEnergyCapAlgebra

/-- Energy allocated to the next cell after the accumulated energy `e`.
Its coefficient uses only quantities already known at that cell's left endpoint. -/
def allocation (K e x : ℝ) : ℝ := min (e + x) K - min e K
def factor (K e x : ℝ) : ℝ := Real.sqrt (allocation K e x / x)

theorem allocation_nonneg (K e : ℝ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ allocation K e x :=
  sub_nonneg.mpr (min_le_min_right K (le_add_of_nonneg_right hx))

theorem allocation_le (K e : ℝ) {x : ℝ} (hx : 0 ≤ x) : allocation K e x ≤ x := by
  by_cases he : e ≤ K
  · rw [allocation, min_eq_left he]
    linarith [min_le_left (e + x) K]
  · have hKe := le_of_not_ge he
    rw [allocation, min_eq_right hKe, min_eq_right (hKe.trans (le_add_of_nonneg_right hx)), sub_self]
    exact hx

theorem factor_nonneg (K e x : ℝ) : 0 ≤ factor K e x := Real.sqrt_nonneg _

theorem factor_le_one (K e : ℝ) {x : ℝ} (hx : 0 ≤ x) : factor K e x ≤ 1 := by
  by_cases hzero : x = 0
  · simp [factor, allocation, hzero]
  · apply Real.sqrt_le_one.mpr
    exact (div_le_one (lt_of_le_of_ne hx (Ne.symm hzero))).mpr (allocation_le K e hx)

theorem energy_eq (K e : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    factor K e x ^ 2 * x = allocation K e x := by
  by_cases hzero : x = 0
  · simp [allocation, hzero]
  · rw [factor, Real.sq_sqrt (div_nonneg (allocation_nonneg K e hx) hx), div_mul_cancel₀ _ hzero]

theorem loss_le (K e : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    (1 - factor K e x) ^ 2 * x ≤ x - allocation K e x := by
  have hq0 := factor_nonneg K e x
  have hq1 := factor_le_one K e hx
  have he := energy_eq K e hx
  have hh : 0 ≤ (2 * factor K e x * (1 - factor K e x)) * x :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hq0) (sub_nonneg.mpr hq1)) hx
  nlinarith

def accumulated (x : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ Finset.range k, x j

theorem allocation_sum (x : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K) (N : ℕ) :
    (∑ k ∈ Finset.range N, allocation K (accumulated x k) (x k)) =
      min (accumulated x N) K := by
  have he (k : ℕ) : accumulated x k + x k = accumulated x (k + 1) :=
    (Finset.sum_range_succ _ _).symm
  simp only [allocation, he]
  rw [Finset.sum_range_sub (fun k ↦ min (accumulated x k) K) N]
  simp [accumulated, min_eq_left hK]

theorem energy_sum (x : ℕ → ℝ) (hx : ∀ k, 0 ≤ x k) (K : ℝ) (hK : 0 ≤ K) (N : ℕ) :
    (∑ k ∈ Finset.range N, factor K (accumulated x k) (x k) ^ 2 * x k) =
      min (accumulated x N) K := by
  simp_rw [energy_eq K _ (hx _)]
  exact allocation_sum x K hK N

/-- Clipping costs at most the energy removed by the cap. -/
theorem total_loss_le (x : ℕ → ℝ) (hx : ∀ k, 0 ≤ x k) (K : ℝ) (hK : 0 ≤ K) (N : ℕ) :
    (∑ k ∈ Finset.range N, (1 - factor K (accumulated x k) (x k)) ^ 2 * x k) ≤
      accumulated x N - min (accumulated x N) K := by
  calc
    _ ≤ ∑ k ∈ Finset.range N, (x k - allocation K (accumulated x k) (x k)) :=
      Finset.sum_le_sum (fun k _ ↦ loss_le K _ (hx k))
    _ = _ := by rw [Finset.sum_sub_distrib, allocation_sum x K hK N]; rfl

theorem excess_le_error {E target K : ℝ} (htarget : target ≤ K) :
    E - min E K ≤ |E - target| := by
  by_cases hE : E ≤ K
  · rw [min_eq_left hE, sub_self]
    exact abs_nonneg _
  · rw [min_eq_right (le_of_not_ge hE)]
    exact (sub_le_sub_left htarget E).trans (le_abs_self _)

end SHEStochastic.SimpleEnergyCapAlgebra
