module

public import SHE.ChildCellGeometry
public import SHE.GaussianPeriodizedLocal

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NodeKernelLocal
open Set AddCircle FiniteHaar ChildCellGeometry
local instance nodeKernelLocal_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

def centeredRow (p : List Bool) (t : ℝ) (ht : 0 < t) (x : AddCircle (1:ℝ)) :
    C(AddCircle (1:ℝ),ℂ) where
  toFun y := HeatMarkov.kernel t ht (x-y)-HeatMarkov.kernel t ht (x-nodeCenter p)
  continuous_toFun := ((HeatMarkov.kernel t ht).continuous.comp
    (continuous_const.sub continuous_id)).sub continuous_const

def constant (p : List Bool) (t : ℝ) (ht : 0 < t) (x : AddCircle (1:ℝ)) : ℝ :=
  (Real.sqrt 8*Real.exp (1/4:ℝ)/Real.sqrt t)*
    ‖HeatMarkov.kernel (8*t) (by positivity) (x-nodeCenter p)‖

theorem constant_nonneg (p : List Bool) {t : ℝ} (ht : 0 < t) (x : AddCircle (1:ℝ)) :
    0 ≤ constant p t ht x := by unfold constant; positivity

theorem kernel_norm_pos {t : ℝ} (ht : 0 < t) (x : AddCircle (1:ℝ)) :
    0 < ‖HeatMarkov.kernel t ht x‖ := by
  have hs := GaussianPeriodizedLocal.gaussian_summable ht (coordinate x)
  have hterm := hs.le_tsum 0 (fun n _ => (Real.exp_pos _).le)
  have hsum : 0 < ∑' n : ℤ,LineGaussianLocal.gaussian t (coordinate x+(n:ℝ)) :=
    (Real.exp_pos _).trans_le hterm
  rw [← coe_coordinate x,GaussianPeriodizedLocal.kernel_coe_norm ht]
  exact mul_pos (inv_pos.mpr (FourierHeatLine.heatMass_pos ht)) hsum

theorem constant_pos (p : List Bool) {t : ℝ} (ht : 0 < t) (x : AddCircle (1:ℝ)) :
    0 < constant p t ht x := by
  unfold constant
  exact mul_pos (by positivity) (kernel_norm_pos (by positivity) _)

theorem argument_coe (x y : AddCircle (1:ℝ)) :
    ((coordinate x-coordinate y:ℝ):AddCircle (1:ℝ))=x-y := by
  rw [QuotientAddGroup.mk_sub,coe_coordinate,coe_coordinate]

theorem center_argument_coe (p : List Bool) (x : AddCircle (1:ℝ)) :
    ((coordinate x-nodeLeft p:ℝ):AddCircle (1:ℝ))=x-nodeCenter p := by
  rw [QuotientAddGroup.mk_sub,coe_coordinate,coe_nodeLeft]

theorem child_near {p : List Bool} {b : Bool} {y : AddCircle (1:ℝ)} {t : ℝ}
    (hsmall : nodeLength p ≤ Real.sqrt t)
    (hy : y ∈ cellSet (p.length+1) (bottomLeaf p b)) (x : AddCircle (1:ℝ)) :
    |(coordinate x-coordinate y)-(coordinate x-nodeLeft p)| ≤ Real.sqrt t := by
  have hb := node_coordinate hy
  rw [show (coordinate x-coordinate y)-(coordinate x-nodeLeft p)=
    -(coordinate y-nodeLeft p) by ring,abs_neg,abs_of_nonneg hb.1]
  exact hb.2.trans hsmall

/-- The actual centered heat row has the small amplitude required by
the negative-input packet, with a localized enlarged heat envelope. -/
theorem row_amplitude (p : List Bool) {t : ℝ} (ht : 0 < t)
    (hsmall : nodeLength p ≤ Real.sqrt t) (x : AddCircle (1:ℝ)) (b : Bool)
    (y : AddCircle (1:ℝ)) (hy : y ∈ cellSet (p.length+1) (bottomLeaf p b)) :
    ‖centeredRow p t ht x y‖ ≤ 2*constant p t ht x/((2^(p.length+1):ℕ):ℝ) := by
  have hb := node_coordinate hy
  have hh := GaussianPeriodizedLocal.kernel_difference_bound
    (a := coordinate x-nodeLeft p) (x := coordinate x-coordinate y)
    (y := coordinate x-nodeLeft p) ht (child_near hsmall hy x) (by simp)
  rw [argument_coe,center_argument_coe] at hh
  have ha : |(coordinate x-coordinate y)-(coordinate x-nodeLeft p)| ≤ nodeLength p := by
    rw [show (coordinate x-coordinate y)-(coordinate x-nodeLeft p)=
      -(coordinate y-nodeLeft p) by ring,abs_neg,abs_of_nonneg hb.1]
    exact hb.2
  change ‖centeredRow p t ht x y‖ ≤ constant p t ht x*
    |(coordinate x-coordinate y)-(coordinate x-nodeLeft p)| at hh
  calc
    _ ≤ constant p t ht x*nodeLength p := hh.trans
      (mul_le_mul_of_nonneg_left ha (constant_nonneg p ht x))
    _ = _ := by unfold nodeLength; ring

/-- Within each genuine dyadic child cell the row has the desired
circle-distance Lipschitz bound, with the same localized envelope. -/
theorem row_lipschitz (p : List Bool) {t : ℝ} (ht : 0 < t)
    (hsmall : nodeLength p ≤ Real.sqrt t) (x : AddCircle (1:ℝ)) (b : Bool)
    (y w : AddCircle (1:ℝ)) (hy : y ∈ cellSet (p.length+1) (bottomLeaf p b))
    (hw : w ∈ cellSet (p.length+1) (bottomLeaf p b)) :
    ‖centeredRow p t ht x y-centeredRow p t ht x w‖ ≤ constant p t ht x*dist y w := by
  have hh := GaussianPeriodizedLocal.kernel_difference_bound
    (a := coordinate x-nodeLeft p) (x := coordinate x-coordinate y)
    (y := coordinate x-coordinate w) ht (child_near hsmall hy x) (child_near hsmall hw x)
  rw [argument_coe,argument_coe,center_argument_coe] at hh
  have he : centeredRow p t ht x y-centeredRow p t ht x w=
      HeatMarkov.kernel t ht (x-y)-HeatMarkov.kernel t ht (x-w) := by
    change (HeatMarkov.kernel t ht (x-y)-HeatMarkov.kernel t ht (x-nodeCenter p))-
      (HeatMarkov.kernel t ht (x-w)-HeatMarkov.kernel t ht (x-nodeCenter p)) = _
    abel
  rw [he]
  change ‖HeatMarkov.kernel t ht (x-y)-HeatMarkov.kernel t ht (x-w)‖ ≤
    constant p t ht x*|(coordinate x-coordinate y)-(coordinate x-coordinate w)| at hh
  rw [show (coordinate x-coordinate y)-(coordinate x-coordinate w)=
    -(coordinate y-coordinate w) by ring,abs_neg,← child_distance hy hw] at hh
  exact hh

end SHE.NodeKernelLocal
