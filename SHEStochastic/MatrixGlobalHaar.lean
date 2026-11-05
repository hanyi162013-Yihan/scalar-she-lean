module

public import SHEStochastic.MatrixHaarRootColumns
public import SHEStochastic.MatrixHaarMass
public import SHE.HaarCellEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.MatrixGlobalHaar
open MeasureTheory SHE SHE.FiniteHaar MatrixHaarFunctions
open scoped NNReal MatrixOrder Matrix.Norms.L2Operator

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
abbrev Physical := Lp (EuclideanSpace ℝ d) 2 μ

def child (p : List Bool) (b : Bool) : Set (AddCircle (1 : ℝ)) :=
  cellSet (p.length+1) (bottomLeaf p b)

theorem child_measurable (p : List Bool) (b : Bool) : MeasurableSet (child p b) :=
  measurableSet_cellSet _ _

theorem child_disjoint (p : List Bool) : Disjoint (child p false) (child p true) :=
  cellSet_disjoint _ _ _ (bottomLeaf_ne p)

theorem cell_positive (n : ℕ) (i : Grid n) : 0 < μ (cellSet n i) := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have he : cellIndicator n i = 0 := by
    apply Lp.ext
    filter_upwards [cellIndicator_ae n i, measure_eq_zero_iff_ae_notMem.mp hz,
      Lp.coeFn_zero ℂ 2 μ] with x hc hx hzero
    rw [hc, Set.indicator_of_notMem hx, hzero]
    rfl
  have hp : 0 < ‖cellIndicator n i‖^2 := by
    rw [cellIndicator_norm_sq]
    positivity
  simpa [he] using hp

/-- A single actual countable covariance-adapted family. A finite path
names its literal two circle cells; the root uses the total mass. -/
def column (κ : AddCircle (1 : ℝ) → Matrix d d ℝ) : HaarNode → d → Physical (d := d)
  | none, i => MatrixHaarRootColumns.root μ κ i
  | some p, i => MatrixHaarLpColumns.vector μ κ (child p false) (child p true)
      (child_measurable p false) (child_measurable p true) i

/-- Every node has the correct actual weighted component Gram matrix.
Ellipticity of its masses is derived from the profile and positive cell
measure, rather than supplied as independent finite matrix data. -/
theorem same_node_gram (κ : AddCircle (1 : ℝ) → Matrix d d ℝ)
    (hκ : Measurable κ) (hInt : Integrable κ μ) (B : ℝ≥0)
    (hBound : ∀ᵐ x ∂μ, ‖κ x‖ ≤ B) (m : ℝ) (hm : 0 < m)
    (hLo : ∀ᵐ x ∂μ, m • (1 : Matrix d d ℝ) ≤ κ x)
    (q : HaarNode) (i j : d) :
    inner ℝ (column κ q i) (MatrixFieldOperator.operator κ hκ B hBound (column κ q j)) =
      if i=j then 1 else 0 := by
  cases q with
  | none =>
    apply MatrixHaarRootColumns.weighted_gram μ κ hκ hInt B hBound
    have hp := MatrixHaarMass.posDef μ κ hInt m hm hLo Set.univ (by simp)
    simpa only [mass, Measure.restrict_univ] using hp
  | some p =>
    apply MatrixHaarLpColumns.weighted_gram μ κ hκ hInt B hBound
      (child p false) (child p true) (child_measurable p false) (child_measurable p true)
      (child_disjoint p)
    · exact MatrixHaarMass.posDef μ κ hInt m hm hLo _ (cell_positive _ _)
    · exact MatrixHaarMass.posDef μ κ hInt m hm hLo _ (cell_positive _ _)


/-- The actual root is orthogonal to every actual detail block. -/
theorem root_detail (κ : AddCircle (1 : ℝ) → Matrix d d ℝ)
    (hκ : Measurable κ) (hInt : Integrable κ μ) (B : ℝ≥0)
    (hBound : ∀ᵐ x ∂μ, ‖κ x‖ ≤ B) (m : ℝ) (hm : 0 < m)
    (hLo : ∀ᵐ x ∂μ, m • (1 : Matrix d d ℝ) ≤ κ x)
    (p : List Bool) (i j : d) :
    inner ℝ (column κ none i) (MatrixFieldOperator.operator κ hκ B hBound (column κ (some p) j)) = 0 := by
  apply MatrixHaarRootColumns.constant_detail μ κ hκ hInt B hBound
    (MatrixFiniteHaar.inverseSqrt (∫ x, κ x ∂μ))
    (child p false) (child p true) (child_measurable p false) (child_measurable p true)
  · exact MatrixHaarMass.posDef μ κ hInt m hm hLo _ (cell_positive _ _)
  · exact MatrixHaarMass.posDef μ κ hInt m hm hLo _ (cell_positive _ _)

/-- Support belongs to the actual periodic dyadic cell named by the
binary path, at every resolution of the countable family. -/
theorem supported (κ : AddCircle (1 : ℝ) → Matrix d d ℝ) (p : List Bool) (i : d) :
    ∀ᵐ x ∂μ, x∉nodeCell p → column κ (some p) i x=0 := by
  filter_upwards [MatrixHaarLpColumns.vector_ae μ κ (child p false) (child p true)
    (child_measurable p false) (child_measurable p true) i] with x hx
  intro hn
  change MatrixHaarLpColumns.vector μ κ (child p false) (child p true)
    (child_measurable p false) (child_measurable p true) i x=0
  rw [hx]
  have hz := MatrixHaarFunctions.support μ κ (child p false) (child p true) x hn
  simp [MatrixHaarLpColumns.raw, hz]


/-- The actual physical factor columns are the covariance multiplier
applied to the countable weighted Haar family. -/
def physicalColumn (κ : AddCircle (1 : ℝ) → Matrix d d ℝ)
    (hκ : Measurable κ) (B : ℝ≥0) (hBound : ∀ᵐ x ∂μ, ‖κ x‖ ≤ B)
    (q : HaarNode) (i : d) : Physical (d := d) :=
  MatrixFieldOperator.operator κ hκ B hBound (column κ q i)

/-- Actual vector-valued spatial cancellation, for use by heat and
negative-norm estimates of the infinite physical factor columns. -/
theorem mean_zero (κ : AddCircle (1 : ℝ) → Matrix d d ℝ)
    (hκ : Measurable κ) (hInt : Integrable κ μ) (B : ℝ≥0)
    (hBound : ∀ᵐ x ∂μ, ‖κ x‖ ≤ B) (m : ℝ) (hm : 0 < m)
    (hLo : ∀ᵐ x ∂μ, m • (1 : Matrix d d ℝ) ≤ κ x)
    (p : List Bool) (i : d) : (∫ x, physicalColumn κ hκ B hBound (some p) i x ∂μ)=0 := by
  let H := fun x => MatrixHaarFunctions.column μ κ (child p false) (child p true) x
  have hIntH := MatrixHaarFunctions.integrable_weighted μ κ hInt (child p false) (child p true)
    (child_measurable p false) (child_measurable p true)
  have hmean := MatrixHaarFunctions.weighted_mean μ κ hInt (child p false) (child p true)
    (child_measurable p false) (child_measurable p true)
    (MatrixHaarMass.posDef μ κ hInt m hm hLo _ (cell_positive _ _))
    (MatrixHaarMass.posDef μ κ hInt m hm hLo _ (cell_positive _ _))
  have hh := (MatrixHaarRootColumns.columnMap i).integral_comp_comm hIntH
  rw [hmean, map_zero] at hh
  apply Eq.trans _ hh
  apply integral_congr_ae
  filter_upwards [MatrixHaarLpColumns.vector_ae μ κ (child p false) (child p true)
    (child_measurable p false) (child_measurable p true) i,
    BoundedFieldOperator.operator_ae (MatrixFieldOperator.field κ hκ B hBound)
      (column κ (some p) i)] with x hv hop
  change BoundedFieldOperator.operator (MatrixFieldOperator.field κ hκ B hBound) (column κ (some p) i) x = _
  rw [hop]
  change Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (κ x)
    (MatrixHaarLpColumns.vector μ κ (child p false) (child p true)
      (child_measurable p false) (child_measurable p true) i x) = _
  rw [hv]
  exact (MatrixHaarRootColumns.column_mul (κ x) (H x) i).symm

end SHEStochastic.MatrixGlobalHaar
