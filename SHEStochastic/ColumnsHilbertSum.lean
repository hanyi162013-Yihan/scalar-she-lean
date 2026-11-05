module

public import SHE.HilbertColumnMap
public import SHEStochastic.L2HilbertSum

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.ColumnsHilbertSum
open SHE.HilbertColumns
open scoped ENNReal

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Reuse the existing column map when its coefficient map is an isometry. -/
def mapIsometry (L : E →ₗᵢ[ℝ] F) : Space ι E →ₗᵢ[ℝ] Space ι F where
  toLinearMap := mapLinear L.toContinuousLinearMap
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq, norm_sq]
    apply tsum_congr
    intro i
    exact congrArg (fun r : ℝ => r ^ 2) (L.norm_map (v i))

theorem mapIsometry_apply (L : E →ₗᵢ[ℝ] F) (v : Space ι E) (i : ι) :
    mapIsometry L v i = L (v i) := rfl

theorem mapIsometry_single [DecidableEq ι] (L : E →ₗᵢ[ℝ] F) (i : ι) (v : E) :
    mapIsometry L (lp.single 2 i v) = lp.single 2 i (L v) :=
  mapCLM_single L.toContinuousLinearMap i v

end SHEStochastic.ColumnsHilbertSum

namespace SHEStochastic.ColumnsHilbertSum
open SHE.HilbertColumns
open scoped ENNReal

variable {ι κ E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] (b : HilbertBasis κ ℝ E)

def unit (j : κ) : ℝ →ₗᵢ[ℝ] E :=
  LinearIsometry.toSpanSingleton ℝ E (b.orthonormal.1 j)

def columnUnit (j : κ) : Space ι ℝ →ₗᵢ[ℝ] Space ι E := mapIsometry (unit b j)

theorem unit_adjoint (j : κ) :
    (unit b j).toContinuousLinearMap.adjoint = innerSL ℝ (b j) := by
  ext x
  simpa [unit, LinearIsometry.toSpanSingleton_apply] using
    (unit b j).toContinuousLinearMap.adjoint_inner_right (1 : ℝ) x

theorem columnUnit_adjoint (j : κ) :
    (columnUnit (ι := ι) b j).toContinuousLinearMap.adjoint = mapCLM (innerSL ℝ (b j)) := by
  ext1 x
  apply ext_inner_left ℝ
  intro v
  calc
    _ = inner ℝ (columnUnit b j v) x :=
      (columnUnit b j).toContinuousLinearMap.adjoint_inner_right _ _
    _ = _ := by
      rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
      apply tsum_congr
      intro i
      change inner ℝ (unit b j (v i)) (x i) = inner ℝ (v i) (innerSL ℝ (b j) (x i))
      rw [← unit_adjoint b j]
      exact ((unit b j).toContinuousLinearMap.adjoint_inner_right _ _).symm

theorem orthogonal :
    OrthogonalFamily ℝ (fun _ : κ => Space ι ℝ) (columnUnit b) := by
  intro j k hjk v w
  rw [lp.inner_eq_tsum]
  have hz (i : ι) : inner ℝ (columnUnit b j v i) (columnUnit b k w i) = 0 :=
    b.orthonormal.orthogonalFamily hjk (v i) (w i)
  simp_rw [hz]
  exact tsum_zero

/-- The same output basis decomposes all square-summable noise columns. -/
theorem total : IsHilbertSum ℝ (fun _ : κ => Space ι ℝ) (columnUnit b) := by
  classical
  let S : Submodule ℝ (Space ι E) :=
    ⨆ j, LinearMap.range (columnUnit b j).toLinearMap
  have hbot : Sᗮ = ⊥ := by
    apply le_antisymm
    · intro x hx
      change x = 0
      apply lp.ext
      funext i
      apply b.repr.injective
      apply lp.ext
      funext j
      have h := (Submodule.mem_orthogonal _ _).mp hx _
        (Submodule.mem_iSup_of_mem j
          (LinearMap.mem_range_self (columnUnit b j).toLinearMap (lp.single 2 i 1)))
      change inner ℝ (mapIsometry (unit b j) (lp.single 2 i 1)) x = 0 at h
      rw [mapIsometry_single, lp.inner_single_left] at h
      simpa only [HilbertBasis.repr_apply_apply, map_zero, lp.coeFn_zero,
        Pi.zero_apply, unit, LinearIsometry.toSpanSingleton_apply, one_smul] using h
    · exact bot_le
  exact IsHilbertSum.mk (orthogonal b) (Submodule.topologicalClosure_eq_top_iff.mpr hbot).ge

theorem unit_total : IsHilbertSum ℝ (fun _ : κ => ℝ) (unit b) :=
  b.orthonormal.isHilbertSum b.dense_span.ge

end SHEStochastic.ColumnsHilbertSum
