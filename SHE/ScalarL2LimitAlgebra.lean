module

public import SHE.WeightedHistoryL2Limit

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace SHE.ScalarL2LimitAlgebra
open Filter MeasureTheory
open scoped Topology
variable {I Ω:Type*} [MeasurableSpace Ω] (μ:Measure Ω)

theorem sub (F G:I→Ω→ℝ) (hF:∀i,Measurable (F i)) (hG:∀i,Measurable (G i))
    (hiF:∀i,Integrable (fun ω=>‖F i ω‖^2) μ) (hiG:∀i,Integrable (fun ω=>‖G i ω‖^2) μ)
    (l:Filter I) (htF:Tendsto (fun i=>∫ω,‖F i ω‖^2 ∂μ) l (𝓝 0))
    (htG:Tendsto (fun i=>∫ω,‖G i ω‖^2 ∂μ) l (𝓝 0)):
    (∀i,Integrable (fun ω=>‖F i ω-G i ω‖^2) μ) ∧
      Tendsto (fun i=>∫ω,‖F i ω-G i ω‖^2 ∂μ) l (𝓝 0):=by
  have hb(i:I)(ω:Ω):‖F i ω-G i ω‖^2≤2*‖F i ω‖^2+2*‖G i ω‖^2:=by
    simp only [Real.norm_eq_abs,sq_abs]
    nlinarith [sq_nonneg (F i ω+G i ω)]
  have hi(i:I):Integrable (fun ω=>‖F i ω-G i ω‖^2) μ:=
    (((hiF i).const_mul 2).add ((hiG i).const_mul 2)).mono'
      (((hF i).sub (hG i)).norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall (fun ω=>by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact hb i ω))
  refine ⟨hi,?_⟩
  have hlim:= (htF.const_mul 2).add (htG.const_mul 2)
  simp only [mul_zero,add_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun i=>integral_nonneg (fun ω=>sq_nonneg _)))
    (Eventually.of_forall (fun i=>?_)) hlim
  calc
    _≤∫ω,2*‖F i ω‖^2+2*‖G i ω‖^2 ∂μ:=integral_mono (hi i)
      (((hiF i).const_mul 2).add ((hiG i).const_mul 2)) (hb i)
    _=2*(∫ω,‖F i ω‖^2 ∂μ)+2*(∫ω,‖G i ω‖^2 ∂μ):=by
      rw [integral_add ((hiF i).const_mul 2) ((hiG i).const_mul 2)]
      simp only [integral_const_mul]

end SHE.ScalarL2LimitAlgebra
