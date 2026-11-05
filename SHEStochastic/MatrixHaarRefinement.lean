module

public import SHEStochastic.MatrixFiniteHaar
public import SHE.SignedPrefix

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixHaarRefinement
open Matrix Finset SHE.FiniteHaar MatrixFiniteHaar

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Coarse data are integrated masses, so the two child masses add
without an averaging or square-root normalization. -/
def parentMass (n : ℕ) (a : Grid (n+1) → Matrix d d ℝ) (x : Grid n) : Matrix d d ℝ :=
  a (leafChild n x false)+a (leafChild n x true)

theorem sum_children (n : ℕ) (a : Grid (n+1) → Matrix d d ℝ) :
    (∑ x, a x)=∑ x, parentMass n a x := by
  ext i j
  simpa only [Matrix.sum_apply, parentMass, Matrix.add_apply] using
    sum_leafChildren n (fun x => a x i j)

theorem total_parent (n : ℕ) (a : Grid (n+1) → Matrix d d ℝ) :
    totalMass n (parentMass n a)=totalMass (n+1) a := (sum_children n a).symm

/-- Every old detail coefficient is exactly unchanged when leaf
masses are aggregated, including for noncommuting matrix data. -/
theorem detail_parent (n : ℕ) (a : Grid (n+1) → Matrix d d ℝ)
    (i : DetailIndex n) (x : Grid (n+1)) :
    MatrixFiniteHaar.detailColumn (n+1) a (detailEmbed n i) x=
      MatrixFiniteHaar.detailColumn n (parentMass n a) i (leafParent n x) := by
  induction n with
  | zero => exact Empty.elim i
  | succ n ih =>
    rcases i with ⟨⟩ | (i | i) <;> rcases x with x | x
    all_goals simp only [detailEmbed, MatrixFiniteHaar.detailColumn, Sum.elim_inl,
      Sum.elim_inr, leafParent]
    · change MatrixHaarAlgebra.left _ _=MatrixHaarAlgebra.left
        (totalMass n (parentMass n (fun y => a (Sum.inl y))))
        (totalMass n (parentMass n (fun y => a (Sum.inr y))))
      rw [total_parent, total_parent]
    · change MatrixHaarAlgebra.right _ _=MatrixHaarAlgebra.right
        (totalMass n (parentMass n (fun y => a (Sum.inl y))))
        (totalMass n (parentMass n (fun y => a (Sum.inr y))))
      rw [total_parent, total_parent]
    · exact ih (fun y => a (Sum.inl y)) i x
    · exact ih (fun y => a (Sum.inr y)) i x

/-- The root and all inherited detail blocks are coherent under a
single dyadic refinement. No positivity is needed for this identity. -/
theorem haar_parent (n : ℕ) (a : Grid (n+1) → Matrix d d ℝ)
    (i : Option (DetailIndex n)) (x : Grid (n+1)) :
    MatrixFiniteHaar.haarColumn (n+1) a (modeEmbed n i) x=
      MatrixFiniteHaar.haarColumn n (parentMass n a) i (leafParent n x) := by
  cases i with
  | none => simp only [modeEmbed, MatrixFiniteHaar.haarColumn, total_parent]
  | some i => exact detail_parent n a i x

theorem parent_fiber (n : ℕ) (a : Grid (n+1) → Matrix d d ℝ) (x : Grid n) :
    (∑ z, if leafParent n z=x then a z else 0)=parentMass n a x := by
  rw [sum_children]
  calc
    _ = ∑ y : Grid n, if y=x then parentMass n a y else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases h : y=x <;> simp [parentMass, leafParent_child, h]
    _ = _ := by simp

/-- Aggregate actual masses over any number of dyadic refinements. -/
def ancestorMass (n : ℕ) : (r : ℕ) → (Grid (n+r) → Matrix d d ℝ) → Grid n → Matrix d d ℝ
  | 0, a => a
  | r+1, a => ancestorMass n r (parentMass (n+r) a)

theorem haar_ancestor (n r : ℕ) (a : Grid (n+r) → Matrix d d ℝ)
    (i : Option (DetailIndex n)) (x : Grid (n+r)) :
    MatrixFiniteHaar.haarColumn (n+r) a (modeLift n r i) x=
      MatrixFiniteHaar.haarColumn n (ancestorMass n r a) i (ancestorLeaf n r x) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    exact (haar_parent (n+r) a (modeLift n r i) x).trans
      (ih (parentMass (n+r) a) (leafParent (n+r) x))

end SHEStochastic.MatrixHaarRefinement
