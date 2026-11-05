module

public import SHE.NodeKernelLocal

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.HeatMarkov
open Set AddCircle ChildCellGeometry GaussianPeriodizedLocal LineGaussianLocal
local instance heatKernelLocal_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

theorem kernel_neg {t : ℝ} (ht : 0 < t) (x : AddCircle (1:ℝ)) :
    kernel t ht (-x)=kernel t ht x := by
  induction x using Quotient.inductionOn with
  | _ r =>
    change kernel t ht ((-r:ℝ):AddCircle (1:ℝ))=kernel t ht (r:AddCircle (1:ℝ))
    rw [kernel_coe_real ht (-r),kernel_coe_real ht r]
    have hs : (∑' n : ℤ,gaussian t (-r+(n:ℝ)))=∑' n : ℤ,gaussian t (r+(n:ℝ)) := by
      calc
        _ = ∑' n : ℤ,gaussian t (r+(((-n):ℤ):ℝ)) := by
          apply tsum_congr
          intro n
          unfold gaussian
          congr 1
          push_cast
          ring
        _ = _ := (Equiv.neg ℤ).tsum_eq (fun n : ℤ => gaussian t (r+(n:ℝ)))
    rw [hs]

def short (z : AddCircle (1:ℝ)) : ℝ := coordinate z-(round (coordinate z):ℤ)

theorem coe_short (z : AddCircle (1:ℝ)) : (short z:AddCircle (1:ℝ))=z := by
  have hi : (((round (coordinate z):ℤ):ℝ):AddCircle (1:ℝ))=0 := by
    apply (AddCircle.coe_eq_zero_iff (1:ℝ)).mpr
    exact ⟨round (coordinate z),by simp only [zsmul_eq_mul,mul_one]⟩
  rw [short,QuotientAddGroup.mk_sub,coe_coordinate,hi,sub_zero]

theorem abs_short (z : AddCircle (1:ℝ)) : |short z|=‖z‖ := by
  have he : ‖(coordinate z:AddCircle (1:ℝ))‖=|short z| := by
    rw [AddCircle.norm_eq]
    simp only [short,inv_one,one_mul,mul_one]
  rw [coe_coordinate] at he
  exact he.symm

def localConstant : ℝ := Real.sqrt 8*Real.exp (1/4:ℝ)

theorem localConstant_pos : 0 < localConstant := by unfold localConstant; positivity

/-- A genuine local circle-translation bound with a normalized enlarged
heat kernel. Its spatial integral is therefore controlled by mass one. -/
theorem kernel_translation_bound {t : ℝ} (ht : 0 < t) (u z : AddCircle (1:ℝ))
    (hz : ‖z‖ ≤ Real.sqrt t) :
    ‖kernel t ht u-kernel t ht (u+z)‖ ≤
      (localConstant/Real.sqrt t)*‖kernel (8*t) (by positivity) u‖*‖z‖ := by
  have hh := GaussianPeriodizedLocal.kernel_difference_bound
    (a := coordinate u) (x := coordinate u) (y := coordinate u+short z) ht
    (by simp) (by simpa only [add_sub_cancel_left,abs_short] using hz)
  have hp : ((coordinate u+short z:ℝ):AddCircle (1:ℝ))=u+z := by
    rw [QuotientAddGroup.mk_add,coe_coordinate,coe_short]
  rw [coe_coordinate,hp] at hh
  rw [show coordinate u-(coordinate u+short z)= -short z by ring,abs_neg,abs_short] at hh
  exact hh

end SHE.HeatMarkov
