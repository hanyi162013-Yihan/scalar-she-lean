module

public import SHEStochastic.MatrixProfileHilbert
public import SHEStochastic.MatrixHaarParameterColumns
public import SHEStochastic.DirectionalAffineProduct
public import SHEStochastic.SpatialRestriction

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixPhysicalColumnMap
open MeasureTheory Matrix MatrixInfiniteHaar MatrixProfileHilbert
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))

def restrictionField (s : Set (AddCircle (1 : ℝ))) (hs : MeasurableSet s) :
    BoundedFieldOperator.Field μ (Fiber d) (Fiber d) := SpatialRestriction.field s hs

def restriction (s : Set (AddCircle (1 : ℝ))) (hs : MeasurableSet s) : Space d →L[ℝ] Space d :=
  BoundedFieldOperator.operator (restrictionField s hs)

theorem restriction_ae (s : Set (AddCircle (1 : ℝ))) (hs : MeasurableSet s) (u : Space d) :
    ⇑(restriction s hs u) =ᵐ[μ] s.indicator u := by
  filter_upwards [BoundedFieldOperator.operator_ae (restrictionField s hs) u] with x hx
  change BoundedFieldOperator.operator (restrictionField s hs) u x=_
  rw [hx]
  by_cases hxs : x∈s <;> simp [restrictionField, SpatialRestriction.field, hxs]

def fiberAction (i : d) : Matrix d d ℝ →L[ℝ] Fiber d →L[ℝ] EuclideanSpace ℝ d :=
  (ContinuousLinearMap.compL ℝ (Fiber d) (Matrix d d ℝ) (EuclideanSpace ℝ d)
      (MatrixHaarRootColumns.columnMap i)).comp
    ((ContinuousLinearMap.precompR (Fiber d) (ContinuousLinearMap.mul ℝ (Matrix d d ℝ)).flip).flip
      (toMatrix d))

theorem fiberAction_apply (i : d) (C : Matrix d d ℝ) (v : Fiber d) :
    fiberAction i C v=MatrixHaarRootColumns.column (toMatrix d v*C) i := rfl

/-- The actual profile/constant-matrix column operation is a bounded
bilinear map on the Frobenius profile Hilbert space. -/
def action (i : d) : Space d →L[ℝ] Matrix d d ℝ →L[ℝ] Physical (d := d) :=
  ((fiberAction i).compLpL₂ 2 μ).flip

theorem action_ae (i : d) (u : Space d) (C : Matrix d d ℝ) :
    ⇑(action i u C) =ᵐ[μ] fun x => MatrixHaarRootColumns.column (toMatrix d (u x)*C) i := by
  convert! (fiberAction i C).coeFn_compLp u using 1 <;> rfl

/-- Restricting the actual matrix profile before the bounded bilinear
operation gives the same literal physical column as multiplying a
constant supported vector by the covariance field. -/
theorem action_restriction (P : Profile d) (s : Set (AddCircle (1 : ℝ))) (hs : MeasurableSet s)
    (i : d) (C : Matrix d d ℝ) :
    action i (restriction s hs (realize d P)) C=
      MatrixFieldOperator.operator P.value P.measurable P.bound P.norm_bound
        (indicatorConstLp 2 hs (measure_ne_top μ s) (MatrixHaarRootColumns.column C i)) := by
  apply Lp.ext
  filter_upwards [action_ae i (restriction s hs (realize d P)) C,
    restriction_ae s hs (realize d P), realize_ae d P,
    indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := measure_ne_top μ s)
      (c := MatrixHaarRootColumns.column C i),
    BoundedFieldOperator.operator_ae (MatrixFieldOperator.field P.value P.measurable P.bound P.norm_bound)
      (indicatorConstLp 2 hs (measure_ne_top μ s) (MatrixHaarRootColumns.column C i))] with x ha hr hp hi hop
  change action i (restriction s hs (realize d P)) C x=
    BoundedFieldOperator.operator (MatrixFieldOperator.field P.value P.measurable P.bound P.norm_bound)
      (indicatorConstLp 2 hs (measure_ne_top μ s) (MatrixHaarRootColumns.column C i)) x
  rw [ha, hop, hi, hr]
  by_cases hx : x∈s
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hp]
    have he : toMatrix d (toVector d (P.value x))=P.value x := (coordinates d).apply_symm_apply _
    rw [he]
    exact MatrixHaarRootColumns.column_mul _ _ i
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, map_zero, zero_mul]
    change MatrixHaarRootColumns.columnMap i 0=Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (P.value x) 0
    rw [map_zero, map_zero]

/-- A physical detail column is a genuine nonlinear map on the
Frobenius profile space, built only from two linear interval masses,
two restrictions and the ordered smooth child coefficient maps. -/
def detail (s t : Set (AddCircle (1 : ℝ))) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (i : d) (u : Space d) : Physical (d := d) :=
  action i (restriction s hs u) (MatrixHaarAlgebra.left (mass d s u) (mass d t u))+
    action i (restriction t ht u) (MatrixHaarAlgebra.right (mass d s u) (mass d t u))

theorem detail_realize (P : Profile d) (s t : Set (AddCircle (1 : ℝ)))
    (hs : MeasurableSet s) (ht : MeasurableSet t) (i : d) :
    detail s t hs ht i (realize d P)=
      MatrixFieldOperator.operator P.value P.measurable P.bound P.norm_bound
        (MatrixHaarLpColumns.vector μ P.value s t hs ht i) := by
  rw [detail, mass_realize, mass_realize, action_restriction, action_restriction, ← map_add,
    ← MatrixHaarParameterColumns.detail_indicators]

theorem global_detail (P : Profile d) (p : List Bool) (i : d) :
    detail (MatrixGlobalHaar.child p false) (MatrixGlobalHaar.child p true)
      (MatrixGlobalHaar.child_measurable p false) (MatrixGlobalHaar.child_measurable p true) i (realize d P)=
        factor P (lp.single 2 (i, some p) 1) := by
  rw [detail_realize, factor_single]
  rfl

end SHEStochastic.MatrixPhysicalColumnMap
