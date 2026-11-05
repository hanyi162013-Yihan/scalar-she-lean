module

public import SHE.DyadicArcs

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ChildCellGeometry
open Set AddCircle FiniteHaar
local instance childCellGeometry_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

def coordinate (y : AddCircle (1:ℝ)) : ℝ := AddCircle.equivIoc (1:ℝ) 0 y
def left (n : ℕ) (x : Grid n) : ℝ := (gridOrdinal n x:ℝ)/((2^n:ℕ):ℝ)
def nodeLeft (p : List Bool) : ℝ := left (p.length+1) (bottomLeaf p false)

theorem coe_coordinate (y : AddCircle (1:ℝ)) : (coordinate y:AddCircle (1:ℝ))=y := AddCircle.coe_equivIoc

theorem coordinate_mem (y : AddCircle (1:ℝ)) : coordinate y ∈ Ioc (0:ℝ) 1 := by
  simpa only [coordinate,zero_add] using (AddCircle.equivIoc (1:ℝ) 0 y).property

theorem cell_coordinate {n : ℕ} {x : Grid n} {y : AddCircle (1:ℝ)} (hy : y ∈ cellSet n x) :
    left n x < coordinate y ∧ coordinate y ≤ left n x+1/((2^n:ℕ):ℝ) := by
  have hc := (DyadicArcs.ceil_mod_interval (2^n) (gridCellEquiv n x) (coordinate_mem y)).mp hy
  rw [gridCellEquiv_val,add_div] at hc
  exact hc

theorem coe_nodeLeft (p : List Bool) : (nodeLeft p:AddCircle (1:ℝ))=nodeCenter p := by
  unfold nodeLeft left nodeCenter DyadicApproximation.cellLeft
  rw [gridCellEquiv_val]

theorem child_left (p : List Bool) (b : Bool) :
    left (p.length+1) (bottomLeaf p b)=nodeLeft p+
      (if b then 1/((2^(p.length+1):ℕ):ℝ) else 0) := by
  cases b
  · simp only [Bool.false_eq_true,ite_false,add_zero]
    rfl
  · simp only [ite_true]
    unfold nodeLeft left
    rw [bottomLeaf_ordinal_adjacent]
    push_cast
    rw [add_div]

/-- The same ordinary representatives place both children in one parent
interval, including the right endpoint of the final periodic cell. -/
theorem node_coordinate {p : List Bool} {b : Bool} {y : AddCircle (1:ℝ)}
    (hy : y ∈ cellSet (p.length+1) (bottomLeaf p b)) :
    0 ≤ coordinate y-nodeLeft p ∧ coordinate y-nodeLeft p ≤ nodeLength p := by
  have hc := cell_coordinate hy
  rw [child_left p b] at hc
  have hN : 0 < (((2^(p.length+1):ℕ):ℝ)) := by positivity
  change 0 ≤ coordinate y-nodeLeft p ∧ coordinate y-nodeLeft p ≤ 2/((2^(p.length+1):ℕ):ℝ)
  rw [show (2:ℝ)/((2^(p.length+1):ℕ):ℝ)=
    1/((2^(p.length+1):ℕ):ℝ)+1/((2^(p.length+1):ℕ):ℝ) by ring]
  cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,add_zero] at hc <;>
    constructor <;> nlinarith [one_div_pos.mpr hN]

theorem child_coordinate_distance {n : ℕ} {x : Grid n} {y w : AddCircle (1:ℝ)}
    (hy : y ∈ cellSet n x) (hw : w ∈ cellSet n x) :
    |coordinate y-coordinate w| ≤ 1/((2^n:ℕ):ℝ) := by
  have hy' := cell_coordinate hy
  have hw' := cell_coordinate hw
  apply abs_le.mpr
  constructor <;> linarith

/-- On a child cell the common ordinary coordinates give exactly the
circle distance, since every child has length at most one half. -/
theorem child_distance {p : List Bool} {b : Bool} {y w : AddCircle (1:ℝ)}
    (hy : y ∈ cellSet (p.length+1) (bottomLeaf p b))
    (hw : w ∈ cellSet (p.length+1) (bottomLeaf p b)) :
    dist y w=|coordinate y-coordinate w| := by
  have hN : 0 < (((2^(p.length+1):ℕ):ℝ)) := by positivity
  have hN2 : (2:ℝ) ≤ (((2^(p.length+1):ℕ):ℝ)) := by
    have hn : 1 ≤ 2^p.length := Nat.one_le_pow _ _ (by norm_num)
    rw [pow_succ,Nat.cast_mul,Nat.cast_ofNat]
    exact_mod_cast (show 2 ≤ 2^p.length*2 by omega)
  have hhalf : (1:ℝ)/((2^(p.length+1):ℕ):ℝ) ≤ 1/2 := by
    apply (div_le_div_iff₀ hN (by norm_num : (0:ℝ) < 2)).mpr
    nlinarith
  calc
    dist y w=dist (coordinate y:AddCircle (1:ℝ)) (coordinate w:AddCircle (1:ℝ)) := by
      rw [coe_coordinate,coe_coordinate]
    _ = _ := by
      rw [dist_eq_norm,← QuotientAddGroup.mk_sub]
      apply (AddCircle.norm_coe_eq_abs_iff (1:ℝ) (by norm_num : (1:ℝ) ≠ 0)).mpr
      simpa only [abs_one] using (child_coordinate_distance hy hw).trans hhalf

end SHE.ChildCellGeometry
