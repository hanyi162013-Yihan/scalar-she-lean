module

public import SHEStochastic.MatrixPhysicalColumnMap
public import SHEStochastic.SpatialRestriction

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixPhysicalColumnStructure
open MeasureTheory Matrix MatrixInfiniteHaar MatrixProfileHilbert MatrixPhysicalColumnMap
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))

theorem action_integral (s : Set (AddCircle (1 : ℝ))) (hs : MeasurableSet s)
    (u : Space d) (i : d) (C : Matrix d d ℝ) :
    (∫ x, action i (restriction s hs u) C x ∂μ)=
      MatrixHaarRootColumns.column (mass d s u*C) i := by
  let L := fiberAction i C
  have hi : Integrable (restriction s hs u) μ :=
    (Lp.memLp _).integrable (by norm_num : (1 : ENNReal)≤2)
  have hr : (∫ x, restriction s hs u x ∂μ)=∫ x in s, u x ∂μ :=
    SpatialRestriction.integral s hs u
  change (∫ x, (L.compLp (restriction s hs u)) x ∂μ)=_
  rw [L.integral_compLp, L.integral_comp_comm hi, hr]
  rfl

/-- Ordinary vector spatial cancellation holds on the full open
positive-mass domain, even for the local `L²` profile extension. -/
theorem mean_zero (s t : Set (AddCircle (1 : ℝ))) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (u : Space d) (i : d) (hA : (mass d s u).PosDef) (hB : (mass d t u).PosDef) :
    (∫ x, detail s t hs ht i u x ∂μ)=0 := by
  let L := MatrixHaarAlgebra.left (mass d s u) (mass d t u)
  let R := MatrixHaarAlgebra.right (mass d s u) (mass d t u)
  have hl : Integrable (action i (restriction s hs u) L) μ :=
    (Lp.memLp _).integrable (by norm_num : (1 : ENNReal)≤2)
  have hr : Integrable (action i (restriction t ht u) R) μ :=
    (Lp.memLp _).integrable (by norm_num : (1 : ENNReal)≤2)
  have ha := integral_congr_ae (Lp.coeFn_add (action i (restriction s hs u) L) (action i (restriction t ht u) R))
  change (∫ x, (action i (restriction s hs u) L+action i (restriction t ht u) R) x ∂μ)=0
  rw [ha]
  simp only [Pi.add_apply]
  rw [integral_add hl hr, action_integral, action_integral]
  have hh := congrArg (MatrixHaarRootColumns.columnMap i) (MatrixHaarAlgebra.weighted_mean _ _ hA hB)
  simpa only [map_add, map_zero, MatrixHaarRootColumns.columnMap_apply] using hh

theorem supported (s t : Set (AddCircle (1 : ℝ))) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (u : Space d) (i : d) : ∀ᵐ x ∂μ, x∉s∪t → detail s t hs ht i u x=0 := by
  let L := MatrixHaarAlgebra.left (mass d s u) (mass d t u)
  let R := MatrixHaarAlgebra.right (mass d s u) (mass d t u)
  filter_upwards [Lp.coeFn_add (action i (restriction s hs u) L) (action i (restriction t ht u) R),
    action_ae i (restriction s hs u) L, action_ae i (restriction t ht u) R,
    restriction_ae s hs u, restriction_ae t ht u] with x ha hl hr hsx htx
  intro hx
  have hxs : x∉s := fun h => hx (Or.inl h)
  have hxt : x∉t := fun h => hx (Or.inr h)
  change (action i (restriction s hs u) L+action i (restriction t ht u) R) x=0
  rw [ha, Pi.add_apply, hl, hr, hsx, htx, Set.indicator_of_notMem hxs, Set.indicator_of_notMem hxt,
    map_zero, zero_mul, zero_mul]
  simp only [MatrixHaarRootColumns.column, map_zero, ContinuousLinearMap.zero_apply, add_zero]

theorem restriction_eq (s t : Set (AddCircle (1 : ℝ))) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (u : Space d) (i : d) :
    SpatialRestriction.operator (s∪t) (hs.union ht) (detail s t hs ht i u)=detail s t hs ht i u := by
  apply Lp.ext
  filter_upwards [SpatialRestriction.operator_ae (s∪t) (hs.union ht) (detail s t hs ht i u),
    supported s t hs ht u i] with x hr hsupp
  rw [hr]
  by_cases hx : x∈s∪t
  · exact Set.indicator_of_mem hx _
  · rw [Set.indicator_of_notMem hx, hsupp hx]

end SHEStochastic.MatrixPhysicalColumnStructure
