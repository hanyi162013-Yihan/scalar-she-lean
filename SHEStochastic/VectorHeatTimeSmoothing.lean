module

public import SHEStochastic.MatrixHeatColumnFlow
public import SHE.HeatTimeSmoothing

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.VectorHeatTimeSmoothing
open MeasureTheory SHE SHE.FiniteHaar SHE.DyadicApproximation MatrixInfiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem real_bound {τ δ θ : ℝ} (hτ : 0 < τ) (hδ : 0 ≤ δ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (v : RealL2) :
    ‖RealHeat.realHeat δ (RealHeat.realHeat τ v)-RealHeat.realHeat τ v‖ ≤ (δ/τ)^θ*‖v‖ := by
  rw [← realEmbed_norm_eq (RealHeat.realHeat δ (RealHeat.realHeat τ v)-RealHeat.realHeat τ v),
    map_sub,RealHeat.realEmbed_realHeat,RealHeat.realEmbed_realHeat]
  exact (HeatTimeSmoothing.heat_increment_bound hτ hδ hθ hθ1 (realEmbed v)).trans_eq
    (by rw [realEmbed_norm_eq])

/-- Vector heat increments inherit the scalar spectral smoothing
constant exactly, without a dimension loss. -/
theorem bound {τ δ θ : ℝ} (hτ : 0 < τ) (hδ : 0 ≤ δ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (v : Physical (d := d)) :
    ‖VectorHeat.heat δ (VectorHeat.heat τ v)-VectorHeat.heat τ v‖ ≤ (δ/τ)^θ*‖v‖ := by
  have hR : 0 ≤ (δ/τ)^θ := Real.rpow_nonneg (div_nonneg hδ hτ.le) θ
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR (norm_nonneg _))).mp
  rw [mul_pow,← VectorHeat.coordinates.norm_map
    (VectorHeat.heat δ (VectorHeat.heat τ v)-VectorHeat.heat τ v),← VectorHeat.coordinates.norm_map v,
    PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have he : VectorHeat.coordinates (VectorHeat.heat δ (VectorHeat.heat τ v)-VectorHeat.heat τ v) i=
      RealHeat.realHeat δ (RealHeat.realHeat τ (VectorHeat.coordinates v i))-
        RealHeat.realHeat τ (VectorHeat.coordinates v i) := by
    rw [map_sub]
    simp only [PiLp.sub_apply,VectorHeat.coordinate_heat]
  rw [he]
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
    (real_bound hτ hδ hθ hθ1 (VectorHeat.coordinates v i)) 2

/-- The same smoothing estimate holds in the complete infinite
Hilbert--Schmidt column space. -/
theorem columns_bound {τ δ θ : ℝ} (hτ : 0 < τ) (hδ : 0 ≤ δ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (v : MatrixHaarKernel.Columns (d := d)) :
    ‖MatrixHeatColumnFlow.operator δ (MatrixHeatColumnFlow.operator τ v)-MatrixHeatColumnFlow.operator τ v‖ ≤
      (δ/τ)^θ*‖v‖ := by
  let L := ((VectorHeat.heat δ)-ContinuousLinearMap.id ℝ (Physical (d := d))).comp (VectorHeat.heat τ)
  have hR : 0 ≤ (δ/τ)^θ := Real.rpow_nonneg (div_nonneg hδ hτ.le) θ
  have hL : ‖L‖ ≤ (δ/τ)^θ :=
    ContinuousLinearMap.opNorm_le_bound _ hR (fun w => bound hτ hδ hθ hθ1 w)
  have he : MatrixHeatColumnFlow.operator δ (MatrixHeatColumnFlow.operator τ v)-
      MatrixHeatColumnFlow.operator τ v=HilbertColumns.mapCLM L v := by
    apply lp.ext
    funext k
    rfl
  rw [he]
  exact (HilbertColumns.map_norm_le L v).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))

end SHEStochastic.VectorHeatTimeSmoothing
