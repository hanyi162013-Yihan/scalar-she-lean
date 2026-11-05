module

public import SHE.OrderedHeatTrees

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.OrderedHeatTrees
open Set MeasureTheory StoppedFourier NativeHeatAction
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

/-- A genuine ordered parent choice, with heat ages supplied by the
original strictly decreasing physical observation times. -/
def ofTimes (κ : ℝ) (hκ : 0 < κ) : (n : ℕ) →
    (t : Fin (n+1) → ℝ) → StrictAnti t →
    ((j : Fin n) → Fin (j.val+1)) → Tree n
  | 0,_,_,_ => .root
  | n+1,t,ht,parent => .branch
      (ofTimes κ hκ n (fun i => t i.castSucc) (fun i j hij => ht hij)
        (fun j => parent j.castSucc))
      (parent (Fin.last n))
      (κ*(t (parent (Fin.last n)).castSucc-t (Fin.last (n+1))))
      (mul_pos hκ (sub_pos.mpr (ht (Fin.castSucc_lt_last _))))

/-- Every root-to-vertex path has exactly the elapsed original physical
age. Parent choices and the number of off-path branches do not change it. -/
theorem age_ofTimes (κ : ℝ) (hκ : 0 < κ) (n : ℕ)
    (t : Fin (n+1) → ℝ) (ht : StrictAnti t)
    (parent : (j : Fin n) → Fin (j.val+1)) (i : Fin (n+1)) :
    age (ofTimes κ hκ n t ht parent) i = κ*(t 0-t i) := by
  induction n with
  | zero =>
    have hi : i = 0 := by apply Fin.ext; omega
    subst i
    simp only [ofTimes,age,sub_self,mul_zero]
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [ofTimes,age,Fin.snoc_last]
      rw [ih]
      have hzero : (0 : Fin (n+1)).castSucc = (0 : Fin (n+2)) := rfl
      rw [hzero]
      ring
    · simp only [ofTimes,age,Fin.snoc_castSucc]
      rw [ih]
      rfl

/-- Actual spatial heat-tree integration retains exactly one terminal
kernel, with the root-to-final-input elapsed age. Every original earlier
parent is permitted at each insertion. -/
theorem timed_endpoint_kernel (κ : ℝ) (hκ : 0 < κ) (n : ℕ)
    (t : Fin (n+1) → ℝ) (ht : StrictAnti t)
    (parent : (j : Fin n) → Fin (j.val+1)) (i : Fin (n+1))
    {q : ℝ} (hq : q < t i) (a b : HeatCircle) :
    average (ofTimes κ hκ n t ht parent)
      (fun z => edge (κ*(t i-q)) (mul_pos hκ (sub_pos.mpr hq)) (z i) b) a =
      edge (κ*(t 0-q)) (by
        have hi : t i ≤ t 0 := ht.antitone (Fin.zero_le i)
        exact mul_pos hκ (by linarith)) a b := by
  have hh := endpoint_kernel (ofTimes κ hκ n t ht parent) i
    (mul_pos hκ (sub_pos.mpr hq)) a b
  simp only [age_ofTimes] at hh
  convert! hh using 1
  congr 1
  ring

end SHE.OrderedHeatTrees
