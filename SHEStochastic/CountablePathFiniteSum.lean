module

public import SHEStochastic.CountablePathConcatenation
public import SHEStochastic.NNRealBlockClock

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic.CountablePathFiniteSum
open CountablePathConcatenation NNRealBlockClock
open scoped NNReal
variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]

theorem clock_after (H t : ℝ≥0) (j : ℕ) (ht : (j+1 : ℕ)*H≤t) :
    clock H j t=H := by
  apply min_eq_right
  apply le_tsub_of_add_le_right
  calc
    H+(j : ℝ≥0)*H = (j+1 : ℕ)*H := by push_cast;ring
    _ ≤ t := ht

/-- A finite concatenation is constant once its last block has ended. -/
theorem finite_after (H : ℝ≥0) (f : ℕ → ℝ≥0 → E) (M : ℕ) (t : ℝ≥0)
    (ht : (M+1 : ℕ)*H≤t) : finite H f M t=finite H f M ((M+1 : ℕ)*H) := by
  cases M with
  | zero => simpa only [finite,Nat.zero_add,Nat.cast_one,one_mul,min_self] using
      congrArg (f 0) (min_eq_right (by simpa using ht))
  | succ M =>
    have he : ((M+1 : ℕ) : ℝ≥0)*H≤((M+1+1 : ℕ) : ℝ≥0)*H := by gcongr;omega
    change finite H f M (min t ((M+1 : ℕ)*H))+
      (f (M+1) (clock H (M+1) t)-f (M+1) 0)=
      finite H f M (min ((M+1+1 : ℕ)*H) ((M+1 : ℕ)*H))+
      (f (M+1) (clock H (M+1) ((M+1+1 : ℕ)*H))-f (M+1) 0)
    rw [min_eq_right (he.trans ht),min_eq_right he,clock_after H t (M+1) ht,
      clock_after H _ (M+1) le_rfl]

theorem finite_clamp (H : ℝ≥0) (f : ℕ → ℝ≥0 → E) (M : ℕ) (t : ℝ≥0) :
    finite H f M (min t ((M+1 : ℕ)*H))=finite H f M t := by
  rcases le_total t ((M+1 : ℕ)*H) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h,finite_after H f M t h]

/-- The anchored recursion equals the literal sum of the elapsed
pieces of the local paths. No endpoint matching hypothesis is needed. -/
theorem finite_sum (H : ℝ≥0) (f : ℕ → ℝ≥0 → E) (M : ℕ) (t : ℝ≥0) :
    finite H f M t=f 0 (clock H 0 t)+
      ∑ j∈Finset.range M,(f (j+1) (clock H (j+1) t)-f (j+1) 0) := by
  induction M with
  | zero => simp [finite,clock]
  | succ M ih =>
    rw [finite,finite_clamp,ih,Finset.sum_range_succ]
    simp only [clock]
    abel

theorem value_sum (H : ℝ≥0) (hH : 0<H) (f : ℕ → ℝ≥0 → E) (M : ℕ) (t : ℝ≥0)
    (ht : t≤(M+1 : ℕ)*H) :
    value H f t=f 0 (clock H 0 t)+
      ∑ j∈Finset.range M,(f (j+1) (clock H (j+1) t)-f (j+1) 0) := by
  rw [value_eq_finite H hH f M t ht,finite_sum]

theorem value_sum_of_zero (H : ℝ≥0) (hH : 0<H) (f : ℕ → ℝ≥0 → E)
    (hf : ∀ j,f j 0=0) (M : ℕ) (t : ℝ≥0) (ht : t≤(M+1 : ℕ)*H) :
    value H f t=∑ j∈Finset.range (M+1),f j (clock H j t) := by
  rw [value_sum H hH f M t ht,Finset.sum_range_succ']
  simp_rw [hf,sub_zero]
  exact add_comm _ _

end SHEStochastic.CountablePathFiniteSum
