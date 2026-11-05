module

public import SHEStochastic.MatrixAnalyticKernel
public import SHE.StrongOperator

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixHeatColumnFlow
open MeasureTheory Filter SHE SHE.FiniteHaar MatrixInfiniteHaar MatrixHaarKernel
open scoped NNReal ENNReal Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]

def operator (t : ℝ) : Columns (d := d) →L[ℝ] Columns (d := d) :=
  HilbertColumns.mapCLM (VectorHeat.heat t)

theorem contraction (t : ℝ) (v : Columns (d := d)) : ‖operator t v‖ ≤ ‖v‖ := by
  have hb : ‖VectorHeat.heat (d := d) t‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun u => by simpa only [one_mul] using VectorHeat.contraction t u)
  exact (HilbertColumns.map_norm_le (VectorHeat.heat t) v).trans
    ((mul_le_mul_of_nonneg_right hb (norm_nonneg v)).trans_eq (one_mul _))

theorem continuous_action (v : Columns (d := d)) : Continuous (fun t : ℝ => operator t v) := by
  classical
  let p (s : Finset (d × HaarNode)) : Columns (d := d) := ∑ i ∈ s, lp.single 2 i (v i)
  have hp : Tendsto p atTop (𝓝 v) := lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) v
  apply StrongOperator.continuous_action_of_approximation (𝕜 := ℝ) (X := ℝ)
    (E := Columns (d := d)) (F := Columns (d := d)) (l := atTop) operator 1 zero_le_one
    (fun t w => by simpa only [one_mul] using contraction t w) v p hp
  intro s
  change Continuous (fun t => operator t (∑ i ∈ s, lp.single 2 i (v i)))
  unfold operator
  simp_rw [map_sum,HilbertColumns.mapCLM_single]
  apply continuous_finsetSum
  intro i hi
  have hi : Continuous (fun t : ℝ => (t,v i)) := continuous_id.prodMk continuous_const
  have hh : Continuous (fun t : ℝ => VectorHeat.heat t (v i)) :=
    Continuous.comp (f := fun t : ℝ => (t,v i))
      (g := fun p : ℝ × Physical (d := d) => VectorHeat.heat p.1 p.2)
      (VectorHeat.continuous_action (d := d)) hi
  have hs : Continuous (fun w : Physical (d := d) =>
      (lp.single 2 i w : Columns (d := d))) :=
    (lp.isometry_single (E := fun _ : d × HaarNode => Physical (d := d)) (p := 2) i).continuous
  exact Continuous.comp (f := fun t : ℝ => VectorHeat.heat t (v i))
    (g := fun w : Physical (d := d) => (lp.single 2 i w : Columns (d := d))) hs hh

theorem forward {t δ : ℝ} (ht : 0 < t) (hδ : 0 ≤ δ) (P : Profile d) :
    kernel (t+δ) P=operator δ (kernel t P) := by
  apply lp.ext
  funext k
  simp only [MatrixHaarKernel.column,if_pos ht,if_pos (add_pos_of_pos_of_nonneg ht hδ),operator,
    HilbertColumns.mapCLM_apply]
  rw [add_comm t δ,VectorHeat.semigroup hδ ht.le]
  rfl

theorem continuousAt_kernel {t : ℝ} (ht : 0 < t) (P : Profile d) :
    ContinuousAt (fun r : ℝ => kernel r P) t := by
  let τ := t/2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτt : τ < t := by dsimp [τ]; linarith
  have he (r : ℝ) (hr : τ < r) : kernel r P=operator (r-τ) (kernel τ P) := by
    simpa only [add_sub_cancel] using forward hτ (sub_nonneg.mpr hr.le) P
  have hc : Continuous (fun r : ℝ => operator (r-τ) (kernel τ P)) :=
    (continuous_action _).comp (continuous_id.sub continuous_const)
  have hlim := hc.tendsto t
  rw [← he t hτt] at hlim
  apply hlim.congr'
  filter_upwards [lt_mem_nhds hτt] with r hr
  exact (he r hr).symm

theorem analytic_forward {t δ : ℝ} (ht : 0 < t) (hδ : 0 ≤ δ) (P : Profile d) :
    MatrixAnalyticKernel.kernel (t+δ) P=
      operator (δ/NativeHeatObservation.timeScale) (MatrixAnalyticKernel.kernel t P) := by
  unfold MatrixAnalyticKernel.kernel
  rw [add_div]
  exact forward (div_pos ht NativeHeatObservation.timeScale_pos)
    (div_nonneg hδ NativeHeatObservation.timeScale_pos.le) P

theorem continuousAt_analytic {t : ℝ} (ht : 0 < t) (P : Profile d) :
    ContinuousAt (fun r : ℝ => MatrixAnalyticKernel.kernel r P) t := by
  have hi : ContinuousAt (fun r : ℝ => r/NativeHeatObservation.timeScale) t :=
    (continuous_id.div_const NativeHeatObservation.timeScale).continuousAt
  exact ContinuousAt.comp (f := fun r : ℝ => r/NativeHeatObservation.timeScale)
    (g := fun r : ℝ => kernel r P)
    (continuousAt_kernel (div_pos ht NativeHeatObservation.timeScale_pos) P) hi

end SHEStochastic.MatrixHeatColumnFlow
