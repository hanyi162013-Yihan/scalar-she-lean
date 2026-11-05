module
public import SHE.HilbertColumns
public import SHE.HaarRiesz
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.FiniteHaarColumnProjection
open MeasureTheory FiniteHaar HilbertColumns Filter
open scoped ENNReal Topology
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
local instance : Fact ((1:ℝ≥0∞)≤2):=⟨by norm_num⟩

/-- Literal finite common-Haar column projection. -/
def projection(F:Finset HaarNode):Space HaarNode E→L[ℝ] Space HaarNode E:=
  ∑i∈F,(lp.singleContinuousLinearMap ℝ (fun _:HaarNode=>E) 2 i).comp
    (lp.evalCLM ℝ (fun _:HaarNode=>E) 2 i)

theorem projection_apply(F:Finset HaarNode)(x:Space HaarNode E):
    projection F x=∑i∈F,lp.single 2 i (x i):=by
  simp only [projection,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,
    lp.singleContinuousLinearMap_apply]
  rfl

theorem coordinate(F:Finset HaarNode)(x:Space HaarNode E)(i:HaarNode):
    projection F x i=if i∈F then x i else 0:=by
  rw [projection_apply]
  simp only [lp.coeFn_sum,Finset.sum_apply,lp.coeFn_single,
    Finset.sum_pi_single,Set.indicator_apply,Finset.mem_coe]

theorem norm_le(F:Finset HaarNode)(x:Space HaarNode E):‖projection F x‖≤‖x‖:=by
  apply lp.norm_mono (by norm_num:(2:ℝ≥0∞)≠0)
  intro i
  rw [coordinate]
  split_ifs <;> simp

theorem norm_sub_le(F:Finset HaarNode)(x y:Space HaarNode E):
    ‖projection F x-y‖≤‖x-y‖+‖projection F y-y‖:=by
  calc
    ‖projection F x-y‖=‖projection F (x-y)+(projection F y-y)‖:=by
      rw [map_sub]
      congr 1
      abel
    _≤‖projection F (x-y)‖+‖projection F y-y‖:=norm_add_le _ _
    _≤‖x-y‖+‖projection F y-y‖:=add_le_add (norm_le F (x-y)) le_rfl

theorem tendsto(x:Space HaarNode E):
    Tendsto (fun n=>projection (nodesBelow n) x) atTop (𝓝 x):=by
  simpa only [projection_apply,Function.comp_def] using
    (lp.hasSum_single (by norm_num:(2:ℝ≥0∞)≠⊤) x).comp nodesBelow_tendsto
end SHE.FiniteHaarColumnProjection
