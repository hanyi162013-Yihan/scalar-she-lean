module

public import SHEStochastic.MatrixHaarRefinement
public import SHEStochastic.MatrixDyadicMass

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixDyadicCoherence
open MeasureTheory SHE SHE.FiniteHaar MatrixHaarRefinement MatrixDyadicMass
open scoped Matrix.Norms.L2Operator

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))

theorem parent (κ : AddCircle (1 : ℝ) → Matrix d d ℝ) (hκ : Integrable κ μ) (n : ℕ) :
    parentMass n (profile κ (n+1))=profile κ n := by
  funext x
  exact (parent_fiber n (profile κ (n+1)) x).symm.trans (refine κ hκ n 1 x).symm

theorem ancestor (κ : AddCircle (1 : ℝ) → Matrix d d ℝ) (hκ : Integrable κ μ) (n r : ℕ) :
    ancestorMass n r (profile κ (n+r))=profile κ n := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change ancestorMass n r (parentMass (n+r) (profile κ ((n+r)+1)))=_
    rw [parent κ hκ]
    exact ih

/-- The same actual covariance-adapted column is present at every
finer grid. The inputs here are literal integrated cell masses. -/
theorem haar (κ : AddCircle (1 : ℝ) → Matrix d d ℝ) (hκ : Integrable κ μ)
    (n r : ℕ) (i : Option (DetailIndex n)) (x : Grid (n+r)) :
    MatrixFiniteHaar.haarColumn (n+r) (profile κ (n+r)) (modeLift n r i) x=
      MatrixFiniteHaar.haarColumn n (profile κ n) i (ancestorLeaf n r x) := by
  rw [haar_ancestor, ancestor κ hκ]

theorem bottom_left (p : List Bool) (a : Grid (p.length+1) → Matrix d d ℝ) :
    MatrixFiniteHaar.detailColumn (p.length+1) a (bottomDetail p) (bottomLeaf p false)=
      MatrixHaarAlgebra.left (a (bottomLeaf p false)) (a (bottomLeaf p true)) := by
  induction p with
  | nil => simp [bottomDetail, bottomLeaf, MatrixFiniteHaar.detailColumn, MatrixFiniteHaar.totalMass]
  | cons b p ih => cases b <;> exact ih _

theorem bottom_right (p : List Bool) (a : Grid (p.length+1) → Matrix d d ℝ) :
    MatrixFiniteHaar.detailColumn (p.length+1) a (bottomDetail p) (bottomLeaf p true)=
      MatrixHaarAlgebra.right (a (bottomLeaf p false)) (a (bottomLeaf p true)) := by
  induction p with
  | nil => simp [bottomDetail, bottomLeaf, MatrixFiniteHaar.detailColumn, MatrixFiniteHaar.totalMass]
  | cons b p ih => cases b <;> exact ih _

theorem bottom_off (p : List Bool) (a : Grid (p.length+1) → Matrix d d ℝ)
    (x : Grid (p.length+1)) (hl : x≠bottomLeaf p false) (hr : x≠bottomLeaf p true) :
    MatrixFiniteHaar.detailColumn (p.length+1) a (bottomDetail p) x=0 := by
  induction p with
  | nil => cases x with
    | inl x => exact False.elim (hl (by cases x; rfl))
    | inr x => exact False.elim (hr (by cases x; rfl))
  | cons b p ih =>
    cases b <;> cases x with
    | inl x =>
      first
      | exact ih _ x (fun h => hl (congrArg Sum.inl h)) (fun h => hr (congrArg Sum.inl h))
      | rfl
    | inr x =>
      first
      | exact ih _ x (fun h => hl (congrArg Sum.inr h)) (fun h => hr (congrArg Sum.inr h))
      | rfl

/-- Literal matrix-valued coefficient of the actual countable family. -/
def coefficient (κ : AddCircle (1 : ℝ) → Matrix d d ℝ) : HaarNode → AddCircle (1 : ℝ) → Matrix d d ℝ
  | none, _ => MatrixFiniteHaar.inverseSqrt (∫ x, κ x ∂μ)
  | some p, x => MatrixHaarFunctions.column μ κ (MatrixGlobalHaar.child p false)
      (MatrixGlobalHaar.child p true) x

theorem column_ae (κ : AddCircle (1 : ℝ) → Matrix d d ℝ) (q : HaarNode) (i : d) :
    ⇑(MatrixGlobalHaar.column κ q i) =ᵐ[μ]
      fun x => MatrixHaarRootColumns.column (coefficient κ q x) i := by
  cases q with
  | none => exact MatrixHaarRootColumns.constant_ae μ _ i
  | some p =>
    exact MatrixHaarLpColumns.vector_ae μ κ _ _
      (MatrixGlobalHaar.child_measurable p false) (MatrixGlobalHaar.child_measurable p true) i

theorem leaf_ancestor_ae (n r : ℕ) :
    ∀ᵐ x ∂μ, ancestorLeaf n r ((gridCellEquiv (n+r)).symm (cellIndex (n+r) x))=
      (gridCellEquiv n).symm (cellIndex n x) := by
  have hh : ∀ᵐ x ∂μ, ∀ i : Grid n, x∈cellSet n i ↔
      ancestorLeaf n r ((gridCellEquiv (n+r)).symm (cellIndex (n+r) x))=i :=
    ae_all_iff.mpr (fun i => DyadicCellRefinement.ancestor_ae n r i)
  filter_upwards [hh] with x hx
  exact (hx _).mp ((cellSet_iff _ _ _).mpr rfl)

/-- At its first grid a detail block has precisely its two actual
child-cell values, and is zero on all other cells. -/
theorem coefficient_bottom (κ : AddCircle (1 : ℝ) → Matrix d d ℝ) (p : List Bool)
    (x : AddCircle (1 : ℝ)) :
    coefficient κ (some p) x=MatrixFiniteHaar.haarColumn (p.length+1)
      (profile κ (p.length+1)) (some (bottomDetail p))
      ((gridCellEquiv (p.length+1)).symm (cellIndex (p.length+1) x)) := by
  let z := (gridCellEquiv (p.length+1)).symm (cellIndex (p.length+1) x)
  have hl : x∈MatrixGlobalHaar.child p false ↔ z=bottomLeaf p false := cellSet_iff _ _ _
  have hr : x∈MatrixGlobalHaar.child p true ↔ z=bottomLeaf p true := cellSet_iff _ _ _
  by_cases hzl : z=bottomLeaf p false
  · have hzr : z≠bottomLeaf p true := by rw [hzl]; exact bottomLeaf_ne p
    simp only [coefficient, MatrixHaarFunctions.column,
      Set.indicator_of_mem (hl.mpr hzl), Set.indicator_of_notMem (fun h => hzr (hr.mp h)),
      add_zero, MatrixFiniteHaar.haarColumn]
    change _=MatrixFiniteHaar.detailColumn _ _ _ z
    rw [hzl, bottom_left]
    rfl
  · by_cases hzr : z=bottomLeaf p true
    · simp only [coefficient, MatrixHaarFunctions.column,
        Set.indicator_of_notMem (fun h => hzl (hl.mp h)), Set.indicator_of_mem (hr.mpr hzr),
        zero_add, MatrixFiniteHaar.haarColumn]
      change _=MatrixFiniteHaar.detailColumn _ _ _ z
      rw [hzr, bottom_right]
      rfl
    · simp only [coefficient, MatrixHaarFunctions.column,
        Set.indicator_of_notMem (fun h => hzl (hl.mp h)),
        Set.indicator_of_notMem (fun h => hzr (hr.mp h)), zero_add, MatrixFiniteHaar.haarColumn]
      exact (bottom_off p _ z hzl hzr).symm

/-- Every actual countable coefficient agrees almost everywhere with
its finite matrix Haar representative at every containing grid. -/
theorem coefficient_grid (κ : AddCircle (1 : ℝ) → Matrix d d ℝ) (hκ : Integrable κ μ)
    (n : ℕ) (q : HaarNode) (hq : nodeDepth q ≤ n) :
    coefficient κ q =ᵐ[μ] fun x => MatrixFiniteHaar.haarColumn n (profile κ n)
      (nodeMode n q hq) ((gridCellEquiv n).symm (cellIndex n x)) := by
  cases q with
  | none =>
    have hn : nodeMode n none hq=none := by
      apply modePath_injective n
      exact modePath_nodeMode n none hq
    filter_upwards with x
    simp only [coefficient, hn, MatrixFiniteHaar.haarColumn, total κ hκ]
  | some p =>
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hq
    rw [nodeMode_lift (nodeDepth (some p)) r (some p) le_rfl hq, nodeMode_some]
    filter_upwards [leaf_ancestor_ae (nodeDepth (some p)) r] with x hx
    rw [haar κ hκ, hx]
    exact coefficient_bottom κ p x

end SHEStochastic.MatrixDyadicCoherence
