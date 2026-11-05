module

public import SHE.HilbertColumnMap
public import SHE.HaarHeatIntegrand
public import SHE.StrongOperator

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.HeatColumnSemigroup
open MeasureTheory Set CircleHeat FiniteHaar HaarHeatIntegrand
open scoped ENNReal Topology
local instance heatColumnSemigroup_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

def operator (t : ℝ) : Columns →L[ℂ] Columns := HilbertColumns.mapCLM (heat t)

theorem operator_apply (t : ℝ) (v : Columns) (q : HaarNode) : operator t v q=heat t (v q) := rfl

theorem operator_contraction (t : ℝ) (v : Columns) : ‖operator t v‖ ≤ ‖v‖ := by
  have hh : ‖heat t‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    (fun w => by simpa only [one_mul] using heat_contraction t w)
  exact (HilbertColumns.map_norm_le (heat t) v).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hh (norm_nonneg v))

theorem continuous_operator_action (v : Columns) : Continuous (fun t => operator t v) := by
  classical
  let P (n : ℕ) : Columns := ∑ q ∈ nodesBelow n,lp.single 2 q (v q)
  have ht : Filter.Tendsto P Filter.atTop (𝓝 v) :=
    (lp.hasSum_single ENNReal.ofNat_ne_top v).comp nodesBelow_tendsto
  apply StrongOperator.continuous_action_of_approximation operator 1 (by norm_num)
    (fun t w => by simpa only [one_mul] using operator_contraction t w) v P ht
  intro n
  change Continuous (fun t => operator t (∑ q ∈ nodesBelow n,lp.single 2 q (v q)))
  unfold operator
  simp_rw [map_sum,HilbertColumns.mapCLM_single]
  apply continuous_finsetSum
  intro q _
  exact (lp.isometry_single (p := 2) q).continuous.comp (continuous_heat_apply (v q))

theorem continuous_operator_joint : Continuous (fun p : ℝ × Columns => operator p.1 p.2) :=
  StrongOperator.continuous_joint_action operator 1 (by norm_num)
    (fun t w => by simpa only [one_mul] using operator_contraction t w) continuous_operator_action

theorem kernel_forward {ell M t δ : ℝ} (hell : 0 < ell) (ht : 0 < t) (hδ : 0 ≤ δ)
    (f : EllipticField ell M) : kernel ell M hell (t+δ,f)=operator δ (kernel ell M hell (t,f)) := by
  apply lp.ext
  funext q
  simp only [operator_apply,kernel_apply,ite_eq_left ht,ite_eq_left (add_pos_of_pos_of_nonneg ht hδ)]
  rw [add_comm t δ,heat_semigroup hδ ht.le]
  rfl

/-- Positive-age continuity holds in the genuine Hilbert--Schmidt column
norm, not merely coordinatewise. -/
theorem continuousAt_kernel {ell M t : ℝ} (hell : 0 < ell) (ht : 0 < t) (f : EllipticField ell M) :
    ContinuousAt (fun r => kernel ell M hell (r,f)) t := by
  let τ := t/2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτt : τ < t := by dsimp [τ]; linarith
  have he (r : ℝ) (hr : τ < r) :
      kernel ell M hell (r,f)=operator (r-τ) (kernel ell M hell (τ,f)) := by
    have hh := kernel_forward hell hτ (sub_nonneg.mpr hr.le) f
    simpa only [add_sub_cancel] using hh
  have hc : Continuous (fun r => operator (r-τ) (kernel ell M hell (τ,f))) :=
    (continuous_operator_action _).comp (continuous_id.sub continuous_const)
  have hlim := hc.tendsto t
  rw [← he t hτt] at hlim
  have heq : (fun r => kernel ell M hell (r,f)) =ᶠ[𝓝 t]
      (fun r => operator (r-τ) (kernel ell M hell (τ,f))) := by
    filter_upwards [lt_mem_nhds hτt] with r hr
    exact he r hr
  exact hlim.congr' heq.symm

end SHE.HeatColumnSemigroup
