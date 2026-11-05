module

public import SHE.ApproximationClock
public import SHE.PredictableSteps

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.ApproximationCells
open MeasureTheory Set ApproximationClock
open scoped NNReal

def index (n : ℕ) (t : ℝ≥0) : ℕ := ⌈(t:ℝ)/delta n⌉₊
def point (n k : ℕ) : ℝ≥0 := ⟨delta n*(k:ℝ),mul_nonneg (delta_pos n).le (Nat.cast_nonneg k)⟩

theorem cell_iff (n k : ℕ) (hk : k ≠ 0) (t : ℝ≥0) :
    t ∈ Ioc (point n (k-1)) (point n k) ↔ index n t=k := by
  rw [index,Nat.ceil_eq_iff hk,lt_div_iff₀ (delta_pos n),div_le_iff₀ (delta_pos n)]
  change delta n*(k-1:ℕ) < (t:ℝ) ∧ (t:ℝ) ≤ delta n*(k:ℝ) ↔
    ((k-1:ℕ):ℝ)*delta n < (t:ℝ) ∧ (t:ℝ) ≤ (k:ℝ)*delta n
  simp only [mul_comm]

theorem index_mem (n : ℕ) {h t : ℝ≥0} (ht : 0 < t) (hth : t ≤ h) :
    index n t ∈ Finset.Icc 1 (index n h) := by
  rw [Finset.mem_Icc]
  constructor
  · exact Nat.one_le_ceil_iff.mpr (div_pos (by exact_mod_cast ht) (delta_pos n))
  · exact Nat.ceil_mono (div_le_div_of_nonneg_right (by exact_mod_cast hth) (delta_pos n).le)

theorem right_eq_point (n : ℕ) (t : ℝ≥0) : right n t=(point n (index n t):ℝ) := rfl

theorem left_eq_point (n : ℕ) {t : ℝ≥0} (ht : 0 < t) :
    left n t=(point n (index n t-1):ℝ) := by
  have hi : 1 ≤ index n t := Nat.one_le_ceil_iff.mpr
    (div_pos (by exact_mod_cast ht) (delta_pos n))
  change delta n*(index n t:ℝ)-delta n=delta n*((index n t-1:ℕ):ℝ)
  rw [Nat.cast_sub hi]
  simp only [Nat.cast_one]
  ring

variable {Ω E : Type*} [AddCommMonoid E]

/-- A finite deterministic partition of time, with arbitrary random
values on the cells. -/
def sum (n : ℕ) (h : ℝ≥0) (Z : ℕ → Ω → E) (p : ℝ≥0 × Ω) : E :=
  ∑ k ∈ Finset.Icc 1 (index n h),
    if p.1 ∈ Ioc (point n (k-1)) (point n k) then Z k p.2 else 0

theorem sum_at (n : ℕ) {h t : ℝ≥0} (ht : 0 < t) (hth : t ≤ h)
    (Z : ℕ → Ω → E) (ω : Ω) : sum n h Z (t,ω)=Z (index n t) ω := by
  classical
  have hi := index_mem n ht hth
  have hin : index n t ≠ 0 := by have := (Finset.mem_Icc.mp hi).1; omega
  unfold sum
  rw [Finset.sum_eq_single (index n t)]
  · rw [ite_eq_left ((cell_iff n _ hin t).mpr rfl)]
  · intro k hk hki
    have hk0 : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
    exact ite_eq_right (fun hh => hki ((cell_iff n k hk0 t).mp hh).symm)
  · intro hnot
    exact False.elim (hnot hi)

end SHE.ApproximationCells
