module

public import SHEStochastic.ColumnsHilbertSum

/-! Tensor a scalar L² isometry with a separable Hilbert output space,
using existing Hilbert decompositions rather than a new stochastic construction. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.HilbertIsometryLift
open MeasureTheory SHE.HilbertColumns ColumnsHilbertSum
open scoped ENNReal

variable {P Ω ι κ E : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Countable κ]
  (ν : Measure P) (μ : Measure Ω) (b : HilbertBasis κ ℝ E)

def sourceEquiv : Lp (Space ι E) 2 ν ≃ₗᵢ[ℝ] lp (fun _ : κ => Lp (Space ι ℝ) 2 ν) 2 :=
  (L2HilbertSum.total ν (columnUnit b) (ColumnsHilbertSum.total b)).linearIsometryEquiv

def targetEquiv : Lp E 2 μ ≃ₗᵢ[ℝ] lp (fun _ : κ => Lp ℝ 2 μ) 2 :=
  (L2HilbertSum.total μ (unit b) (unit_total b)).linearIsometryEquiv

theorem source_coordinate (v : Lp (Space ι E) 2 ν) (j : κ) :
    sourceEquiv ν b v j = ((mapCLM (innerSL ℝ (b j))).compLpL 2 ν) v := by
  change (L2HilbertSum.total ν (columnUnit b) (ColumnsHilbertSum.total b)).linearIsometryEquiv v j = _
  rw [L2HilbertSum.coordinate,
    L2HilbertSum.lift_adjoint ν (columnUnit (ι := ι) b) j, columnUnit_adjoint]

/-- The lifted map is an exact isometry; this is a deterministic L² theorem. -/
def operator (T : Lp (Space ι ℝ) 2 ν →ₗᵢ[ℝ] Lp ℝ 2 μ) :
    Lp (Space ι E) 2 ν →ₗᵢ[ℝ] Lp E 2 μ :=
  (targetEquiv μ b).symm.toLinearIsometry.comp
    ((mapIsometry T).comp (sourceEquiv ν b).toLinearIsometry)

theorem operator_hasSum (T : Lp (Space ι ℝ) 2 ν →ₗᵢ[ℝ] Lp ℝ 2 μ)
    (v : Lp (Space ι E) 2 ν) :
    HasSum (fun j => L2HilbertSum.lift μ (unit b j) (T (sourceEquiv ν b v j)))
      (operator ν μ b T v) :=
  (L2HilbertSum.total μ (unit b) (unit_total b)).hasSum_linearIsometryEquiv_symm
    (mapIsometry T (sourceEquiv ν b v))

theorem operator_basis (T : Lp (Space ι ℝ) 2 ν →ₗᵢ[ℝ] Lp ℝ 2 μ)
    (j : κ) (f : Lp (Space ι ℝ) 2 ν) :
    operator ν μ b T (L2HilbertSum.lift ν (columnUnit b j) f) =
      L2HilbertSum.lift μ (unit b j) (T f) := by
  classical
  have hs : (sourceEquiv ν b).symm (lp.single 2 j f) =
      L2HilbertSum.lift ν (columnUnit b j) f :=
    (L2HilbertSum.total ν (columnUnit b) (ColumnsHilbertSum.total b)).linearIsometryEquiv_symm_apply_single f
  change (targetEquiv μ b).symm
    (mapIsometry T (sourceEquiv ν b (L2HilbertSum.lift ν (columnUnit b j) f))) = _
  rw [← hs, LinearIsometryEquiv.apply_symm_apply, mapIsometry_single]
  exact (L2HilbertSum.total μ (unit b) (unit_total b)).linearIsometryEquiv_symm_apply_single (T f)

theorem output_projection (L : E →L[ℝ] ℝ) (j : κ) (f : Lp ℝ 2 μ) :
    (L.compLpL 2 μ) (L2HilbertSum.lift μ (unit b j) f) = L (b j) • f := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (L2HilbertSum.lift μ (unit b j) f),
    L2HilbertSum.lift_ae μ (unit b j) f, Lp.coeFn_smul (L (b j)) f] with ω hL hf hs
  rw [hL, hf, hs]
  change L (f ω • b j) = L (b j) • f ω
  rw [map_smul]
  exact mul_comm _ _

theorem input_projection (L : E →L[ℝ] ℝ) (j : κ) (f : Lp (Space ι ℝ) 2 ν) :
    ((mapCLM L).compLpL 2 ν) (L2HilbertSum.lift ν (columnUnit b j) f) = L (b j) • f := by
  apply Lp.ext
  filter_upwards [(mapCLM L).coeFn_compLpL (L2HilbertSum.lift ν (columnUnit b j) f),
    L2HilbertSum.lift_ae ν (columnUnit b j) f, Lp.coeFn_smul (L (b j)) f] with p hL hf hs
  rw [hL, hf, hs]
  apply lp.ext
  funext i
  change L (f p i • b j) = L (b j) • f p i
  rw [map_smul]
  exact mul_comm _ _

/-- Every continuous scalar projection commutes with the same lifted
operator. This is the naturality required by the stochastic interface. -/
theorem commutes (T : Lp (Space ι ℝ) 2 ν →ₗᵢ[ℝ] Lp ℝ 2 μ) (L : E →L[ℝ] ℝ)
    (v : Lp (Space ι E) 2 ν) :
    (L.compLpL 2 μ) (operator ν μ b T v) = T (((mapCLM L).compLpL 2 ν) v) := by
  classical
  let A := (L.compLpL 2 μ).comp (operator ν μ b T).toContinuousLinearMap
  let B := T.toContinuousLinearMap.comp ((mapCLM L).compLpL 2 ν)
  have heq : A.comp (sourceEquiv ν b).symm.toContinuousLinearEquiv.toContinuousLinearMap =
      B.comp (sourceEquiv ν b).symm.toContinuousLinearEquiv.toContinuousLinearMap := by
    apply lp.ext_continuousLinearMap (by simp)
    intro j
    ext1 f
    change A ((sourceEquiv ν b).symm (lp.single 2 j f)) =
      B ((sourceEquiv ν b).symm (lp.single 2 j f))
    rw [show (sourceEquiv ν b).symm (lp.single 2 j f) =
      L2HilbertSum.lift ν (columnUnit b j) f from
      (L2HilbertSum.total ν (columnUnit b) (ColumnsHilbertSum.total b)).linearIsometryEquiv_symm_apply_single f]
    change (L.compLpL 2 μ) (operator ν μ b T (L2HilbertSum.lift ν (columnUnit b j) f)) =
      T (((mapCLM L).compLpL 2 ν) (L2HilbertSum.lift ν (columnUnit b j) f))
    rw [operator_basis, output_projection, input_projection, map_smul]
  have h := congrArg (fun U => U (sourceEquiv ν b v)) heq
  change A ((sourceEquiv ν b).symm (sourceEquiv ν b v)) =
    B ((sourceEquiv ν b).symm (sourceEquiv ν b v)) at h
  rw [LinearIsometryEquiv.symm_apply_apply] at h
  exact h

end SHEStochastic.HilbertIsometryLift
