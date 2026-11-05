module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic.NNRealBlockClock
open scoped NNReal

/-- Length of the part of [0,t] lying in the j-th fixed block. -/
def clock (H : ℝ≥0) (j : ℕ) (t : ℝ≥0) : ℝ≥0 := min (t-(j : ℝ≥0)*H) H

theorem clock_le (H : ℝ≥0) (j : ℕ) (t : ℝ≥0) : clock H j t≤H := min_le_right _ _

theorem split (t a b : ℝ≥0) : min t a+min (t-a) b=min t (a+b) := by
  by_cases ht : t≤a
  · rw [min_eq_left ht,tsub_eq_zero_of_le ht,min_eq_left (show (0 : ℝ≥0)≤b from bot_le),add_zero,
      min_eq_left (ht.trans (le_add_of_nonneg_right bot_le))]
  · have ha : a≤t := (le_of_not_ge ht)
    rw [min_eq_right ha]
    have he : t=a+(t-a) := (add_tsub_cancel_of_le ha).symm
    conv_rhs => rw [he,min_add_add_left]

/-- Finite block clocks cover exactly the original elapsed time. -/
theorem sum_clock (H t : ℝ≥0) (M : ℕ) :
    (∑ j∈Finset.range (M+1),clock H j t)=min t ((M+1 : ℕ)*H) := by
  induction M with
  | zero => simp [clock]
  | succ M ih =>
    rw [Finset.sum_range_succ,ih,clock]
    have h := split t ((M+1 : ℕ)*H) H
    calc
      _ = min t (((M+1 : ℕ) : ℝ≥0)*H+H) := h
      _ = _ := by congr 1;push_cast;ring

theorem sum_clock_eq (H t : ℝ≥0) (M : ℕ) (ht : t≤(M+1 : ℕ)*H) :
    (∑ j∈Finset.range (M+1),clock H j t)=t := by rw [sum_clock,min_eq_left ht]

/-- Taking a Brownian covariance minimum commutes with cutting time
into the fixed blocks; repeated or differently timed coordinates stay exact. -/
theorem clock_min (H : ℝ≥0) (j : ℕ) (s t : ℝ≥0) :
    min (clock H j s) (clock H j t)=clock H j (min s t) := by
  rcases le_total s t with h | h
  · have hc : clock H j s≤clock H j t := min_le_min (tsub_le_tsub_right h _) le_rfl
    rw [min_eq_left hc,min_eq_left h]
  · have hc : clock H j t≤clock H j s := min_le_min (tsub_le_tsub_right h _) le_rfl
    rw [min_eq_right hc,min_eq_right h]

theorem clock_terminal (H : ℝ≥0) (j M : ℕ) (hj : j+1≤M) :
    clock H j ((M : ℝ≥0)*H)=H := by
  apply min_eq_right
  apply le_tsub_of_add_le_right
  have hc : ((j+1 : ℕ) : ℝ≥0)≤(M : ℝ≥0) := by exact_mod_cast hj
  calc
    H+(j : ℝ≥0)*H = ((j+1 : ℕ) : ℝ≥0)*H := by push_cast;ring
    _ ≤ (M : ℝ≥0)*H := mul_le_mul_of_nonneg_right hc (show (0 : ℝ≥0)≤H from bot_le)

theorem sum_min (H s t : ℝ≥0) (M : ℕ) (hs : s≤(M+1 : ℕ)*H) (ht : t≤(M+1 : ℕ)*H) :
    (∑ j∈Finset.range (M+1),min (clock H j s) (clock H j t))=min s t := by
  simp_rw [clock_min]
  exact sum_clock_eq H (min s t) M ((min_le_left _ _).trans hs)

end SHEStochastic.NNRealBlockClock
