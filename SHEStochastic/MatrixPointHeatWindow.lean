module

public import SHEStochastic.MatrixPointHeatRows

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.MatrixPointHeatWindow
open MeasureTheory SHE SHE.StoppedFourier MatrixInfiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- A stopping endpoint bounds an original-target heat row without
changing the target or the profile's own physical time parameter. -/
theorem norm_sq (P : Profile d) {T b r U : ℝ} (hP : P.upper ≤ U) (hbT : b ≤ T) (hrb : r < b)
    (x : HeatCircle) (i : d) :
    ‖MatrixPointHeatRows.row (T-r) P x i‖^2 ≤ U*(1+heatConstant*(b-r)^(-(1/2 : ℝ))) := by
  have ht : 0 < T-r := by linarith
  have hU : 0 ≤ U := P.upper_pos.le.trans hP
  refine (MatrixPointHeatRows.norm_sq ht P x i).trans ?_
  have hp := Real.rpow_le_rpow_of_nonpos (sub_pos.mpr hrb) (by linarith : b-r ≤ T-r) (by norm_num : -(1/2 : ℝ) ≤ 0)
  have he := mul_le_mul_of_nonneg_left hp heatConstant_pos.le
  exact (mul_le_mul_of_nonneg_left (add_le_add le_rfl he) P.upper_pos.le).trans
    (mul_le_mul_of_nonneg_right hP (add_nonneg zero_le_one
      (mul_nonneg heatConstant_pos.le (Real.rpow_nonneg (sub_pos.mpr hrb).le _))))

end SHEStochastic.MatrixPointHeatWindow
