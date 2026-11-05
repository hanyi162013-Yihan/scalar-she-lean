module

public import SHE.NativeHeatForestEndpoint

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000
noncomputable section

namespace SHE.OrderedHeatForests
open Set MeasureTheory StoppedFourier NativeHeatAction
open scoped BigOperators
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] NativeHeatAction.edge NativeHeatSpan.kernel

/-- Every insertion can select any member of its actual earlier finite
frame. The original roots need not have equal times or centers. -/
def Choices (m : ℕ) : ℕ → Type
  | 0 => Unit
  | k+1 => Choices m k × Fin (m+k)

instance choicesFintype (m k : ℕ) : Fintype (Choices m k) := by
  induction k with
  | zero => change Fintype Unit; infer_instance
  | succ k ih =>
    change Fintype (Choices m k × Fin (m+k))
    letI : Fintype (Choices m k) := ih
    infer_instance

def OrderedTimes {m : ℕ} : (k : ℕ) → (Fin (m+k) → ℝ) → Prop
  | 0,_ => True
  | k+1,t => OrderedTimes k (fun i => t i.succ) ∧ ∀ i : Fin (m+k), t 0 < t i.succ

def ofChoices {m : ℕ} (κ : ℝ) (hκ : 0 < κ) :
    (k : ℕ) → (t : Fin (m+k) → ℝ) → OrderedTimes k t → Choices m k → Forest m k
  | 0,_,_,_ => .roots
  | k+1,t,ht,Q => .branch
      (ofChoices κ hκ k (fun i => t i.succ) ht.1 Q.1) Q.2
      (κ*(t Q.2.succ-t 0)) (mul_pos hκ (sub_pos.mpr (ht.2 Q.2)))

theorem ofChoices_compatible {m : ℕ} (κ : ℝ) (hκ : 0 < κ) (k : ℕ)
    (t : Fin (m+k) → ℝ) (ht : OrderedTimes k t) (Q : Choices m k) :
    TimeCompatible κ (ofChoices κ hκ k t ht Q) t := by
  induction k with
  | zero => trivial
  | succ k ih => exact ⟨ih _ ht.1 Q.1,rfl⟩

/-- The literal product of all original earlier-parent heat sums. -/
def parentDensity {m : ℕ} (κ : ℝ) (hκ : 0 < κ) :
    (k : ℕ) → (t : Fin (m+k) → ℝ) → OrderedTimes k t → (Fin (m+k) → HeatCircle) → ℝ
  | 0,_,_,_ => 1
  | k+1,t,ht,z => parentDensity κ hκ k (fun i => t i.succ) ht.1 (fun i => z i.succ)*
      ∑ i : Fin (m+k), edge (κ*(t i.succ-t 0)) (mul_pos hκ (sub_pos.mpr (ht.2 i))) (z i.succ) (z 0)

/-- Expanding the actual parent sums gives exactly the finite ordered
forest family, with no replacement of locations or observation ages. -/
theorem sum_density_eq {m : ℕ} (κ : ℝ) (hκ : 0 < κ) (k : ℕ)
    (t : Fin (m+k) → ℝ) (ht : OrderedTimes k t) (z : Fin (m+k) → HeatCircle) :
    (∑ Q : Choices m k, density (ofChoices κ hκ k t ht Q) z) = parentDensity κ hκ k t ht z := by
  induction k with
  | zero => simp only [Choices,ofChoices,density,parentDensity,Finset.sum_const,Finset.card_univ,Fintype.card_unique,one_smul]
  | succ k ih =>
    change (∑ Q : Choices m k × Fin (m+k),
      density (ofChoices κ hκ k (fun i => t i.succ) ht.1 Q.1) (fun i => z i.succ)*
        edge (κ*(t Q.2.succ-t 0)) (mul_pos hκ (sub_pos.mpr (ht.2 Q.2))) (z Q.2.succ) (z 0)) = _
    rw [Fintype.sum_prod_type]
    calc
      _ = (∑ Q : Choices m k, density (ofChoices κ hκ k (fun i => t i.succ) ht.1 Q) (fun i => z i.succ))*
          ∑ i : Fin (m+k), edge (κ*(t i.succ-t 0)) (mul_pos hκ (sub_pos.mpr (ht.2 i))) (z i.succ) (z 0) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro Q _
        rw [Finset.mul_sum]
      _ = _ := by rw [ih]; rfl

theorem rootValues_lt {m k : ℕ} (t : Fin (m+k) → ℝ) {q : ℝ} (hq : ∀ i, q < t i) :
    ∀ i, q < rootValues k t i := by
  induction k with
  | zero => exact hq
  | succ k ih => exact ih (fun i => t i.succ) (fun i => hq i.succ)

end SHE.OrderedHeatForests
