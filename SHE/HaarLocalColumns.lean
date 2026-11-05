module

public import SHE.HaarColumnFormula
public import SHE.HaarDerivativeHeat

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.FiniteHaar
open Finset MeasureTheory AddCircle CircleHeat
local instance haarLocalColumns_periodPos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def bottomDetail : (p : List Bool) → DetailIndex (p.length + 1)
  | [] => Sum.inl ()
  | false :: p => Sum.inr (Sum.inl (bottomDetail p))
  | true :: p => Sum.inr (Sum.inr (bottomDetail p))

def bottomLeaf : (p : List Bool) → Bool → Grid (p.length + 1)
  | [], false => Sum.inl ()
  | [], true => Sum.inr ()
  | false :: p, b => Sum.inl (bottomLeaf p b)
  | true :: p, b => Sum.inr (bottomLeaf p b)

theorem bottomLeaf_ne (p : List Bool) : bottomLeaf p false ≠ bottomLeaf p true := by
  induction p with
  | nil => simp [bottomLeaf]
  | cons b p ih => cases b <;> simpa only [bottomLeaf, ne_eq, Sum.inl.injEq, Sum.inr.injEq] using ih

theorem detailPath_bottomDetail (p : List Bool) : detailPath (p.length + 1) (bottomDetail p) = p := by
  induction p with
  | nil => rfl
  | cons b p ih => cases b <;> simp only [bottomDetail, detailPath, List.length_cons, ih]

theorem nodeMode_some (p : List Bool) :
    nodeMode (nodeDepth (some p)) (some p) le_rfl = some (bottomDetail p) := by
  apply modePath_injective
  rw [modePath_nodeMode]
  exact congrArg some (detailPath_bottomDetail p).symm

theorem detailColumn_bottom_left (p : List Bool) (c : Grid (p.length + 1) → ℝ) :
    detailColumn (p.length + 1) c (bottomDetail p) (bottomLeaf p false) =
      haarLeft (c (bottomLeaf p false)) (c (bottomLeaf p true)) := by
  induction p with
  | nil => simp [bottomDetail, bottomLeaf, detailColumn, totalMass]
  | cons b p ih => cases b <;> exact ih _

theorem detailColumn_bottom_right (p : List Bool) (c : Grid (p.length + 1) → ℝ) :
    detailColumn (p.length + 1) c (bottomDetail p) (bottomLeaf p true) =
      haarRight (c (bottomLeaf p false)) (c (bottomLeaf p true)) := by
  induction p with
  | nil => simp [bottomDetail, bottomLeaf, detailColumn, totalMass]
  | cons b p ih => cases b <;> exact ih _

theorem detailColumn_bottom_off (p : List Bool) (c : Grid (p.length + 1) → ℝ)
    (x : Grid (p.length + 1)) (hl : x ≠ bottomLeaf p false) (hr : x ≠ bottomLeaf p true) :
    detailColumn (p.length + 1) c (bottomDetail p) x = 0 := by
  induction p with
  | nil => cases x with
    | inl x => exact False.elim (hl (by cases x; rfl))
    | inr x => exact False.elim (hr (by cases x; rfl))
  | cons b p ih =>
    cases b <;> cases x with
    | inl x =>
      first
      | exact ih _ x (fun he => hl (congrArg Sum.inl he)) (fun he => hr (congrArg Sum.inl he))
      | rfl
    | inr x =>
      first
      | exact ih _ x (fun he => hl (congrArg Sum.inr he)) (fun he => hr (congrArg Sum.inr he))
      | rfl

theorem bottom_sum {E : Type*} [AddCommMonoid E] (p : List Bool)
    (F : Grid (p.length + 1) → E)
    (hF : ∀ x, x ≠ bottomLeaf p false → x ≠ bottomLeaf p true → F x = 0) :
    (∑ x, F x) = F (bottomLeaf p false) + F (bottomLeaf p true) := by
  classical
  have he : (∑ x ∈ ({bottomLeaf p false, bottomLeaf p true} : Finset _), F x) = ∑ x, F x := by
    apply sum_subset (subset_univ _)
    intro x hx hn
    apply hF x
    · exact fun he => hn (by simp [he])
    · exact fun he => hn (by simp [he])
  rw [← he]
  simp [(bottomLeaf_ne p)]

/-- An arbitrary genuine nonconstant Haar column is exactly the two
child restrictions in the manuscript, on its literal periodic cells. -/
theorem globalHaarColumn_two_children (p : List Bool) (f : CircleL2) :
    globalHaarColumn (some p) f =
      (Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ)) *
        haarLeft (localAverage (p.length + 1) f (bottomLeaf p false))
          (localAverage (p.length + 1) f (bottomLeaf p true))) •
            cellRestriction (p.length + 1) (bottomLeaf p false) f +
      (Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ)) *
        haarRight (localAverage (p.length + 1) f (bottomLeaf p false))
          (localAverage (p.length + 1) f (bottomLeaf p true))) •
            cellRestriction (p.length + 1) (bottomLeaf p true) f := by
  rw [globalHaarColumn, nodeMode_some]
  dsimp only [nodeDepth]
  unfold fixedHaarColumn
  have hs := bottom_sum (E := CircleL2) p
    (fun x : Grid (p.length + 1) =>
      (Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ)) *
        haarColumn (p.length + 1) (localAverage (p.length + 1) f) (some (bottomDetail p)) x) •
          cellRestriction (p.length + 1) x f) (by
    intro x hl hr
    simp only [haarColumn, detailColumn_bottom_off p _ x hl hr, mul_zero, zero_smul])
  convert hs using 1 <;> simp only [haarColumn, detailColumn_bottom_left, detailColumn_bottom_right]
  apply Finset.sum_congr
  · ext x
    simp
  · intro x hx
    rfl

def nodeCell (p : List Bool) : Set (AddCircle (1 : ℝ)) :=
  cellSet (p.length + 1) (bottomLeaf p false) ∪ cellSet (p.length + 1) (bottomLeaf p true)

theorem measurableSet_nodeCell (p : List Bool) : MeasurableSet (nodeCell p) :=
  (measurableSet_cellSet _ _).union (measurableSet_cellSet _ _)

theorem globalHaarColumn_supported (p : List Bool) (f : CircleL2) :
    ∀ᵐ y ∂haarAddCircle, y ∉ nodeCell p → globalHaarColumn (some p) f y = 0 := by
  rw [globalHaarColumn_two_children]
  filter_upwards [Lp.coeFn_add
      ((Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ)) *
        haarLeft (localAverage (p.length + 1) f (bottomLeaf p false))
          (localAverage (p.length + 1) f (bottomLeaf p true))) •
            cellRestriction (p.length + 1) (bottomLeaf p false) f)
      ((Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ)) *
        haarRight (localAverage (p.length + 1) f (bottomLeaf p false))
          (localAverage (p.length + 1) f (bottomLeaf p true))) •
            cellRestriction (p.length + 1) (bottomLeaf p true) f),
      Lp.coeFn_smul (Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ)) *
        haarLeft (localAverage (p.length + 1) f (bottomLeaf p false))
          (localAverage (p.length + 1) f (bottomLeaf p true)))
        (cellRestriction (p.length + 1) (bottomLeaf p false) f),
      Lp.coeFn_smul (Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ)) *
        haarRight (localAverage (p.length + 1) f (bottomLeaf p false))
          (localAverage (p.length + 1) f (bottomLeaf p true)))
        (cellRestriction (p.length + 1) (bottomLeaf p true) f),
      cellRestriction_ae (p.length + 1) (bottomLeaf p false) f,
      cellRestriction_ae (p.length + 1) (bottomLeaf p true) f] with y ha hl hr hcl hcr
  intro hy
  have hyl : y ∉ cellSet (p.length + 1) (bottomLeaf p false) := fun h => hy (Or.inl h)
  have hyr : y ∉ cellSet (p.length + 1) (bottomLeaf p true) := fun h => hy (Or.inr h)
  rw [ha]
  simp only [Pi.add_apply]
  rw [hl, hr]
  simp only [Pi.smul_apply, hcl, hcr, Set.indicator_of_notMem hyl, Set.indicator_of_notMem hyr,
    smul_zero, add_zero]

theorem detailColumnDifferential_bottom_left (p : List Bool) (c h : Grid (p.length + 1) → ℝ) :
    detailColumnDifferential (p.length + 1) c h (bottomDetail p) (bottomLeaf p false) =
      haarLeftDifferential (c (bottomLeaf p false)) (c (bottomLeaf p true))
        (h (bottomLeaf p false)) (h (bottomLeaf p true)) := by
  induction p with
  | nil => simp [bottomDetail, bottomLeaf, detailColumnDifferential, totalMass]
  | cons b p ih => cases b <;> exact ih _ _

theorem detailColumnDifferential_bottom_right (p : List Bool) (c h : Grid (p.length + 1) → ℝ) :
    detailColumnDifferential (p.length + 1) c h (bottomDetail p) (bottomLeaf p true) =
      haarRightDifferential (c (bottomLeaf p false)) (c (bottomLeaf p true))
        (h (bottomLeaf p false)) (h (bottomLeaf p true)) := by
  induction p with
  | nil => simp [bottomDetail, bottomLeaf, detailColumnDifferential, totalMass]
  | cons b p ih => cases b <;> exact ih _ _

theorem detailColumnDifferential_bottom_off (p : List Bool) (c h : Grid (p.length + 1) → ℝ)
    (x : Grid (p.length + 1)) (hl : x ≠ bottomLeaf p false) (hr : x ≠ bottomLeaf p true) :
    detailColumnDifferential (p.length + 1) c h (bottomDetail p) x = 0 := by
  induction p with
  | nil => cases x with
    | inl x => exact False.elim (hl (by cases x; rfl))
    | inr x => exact False.elim (hr (by cases x; rfl))
  | cons b p ih =>
    cases b <;> cases x with
    | inl x =>
      first
      | exact ih _ _ x (fun he => hl (congrArg Sum.inl he)) (fun he => hr (congrArg Sum.inl he))
      | rfl
    | inr x =>
      first
      | exact ih _ _ x (fun he => hl (congrArg Sum.inr he)) (fun he => hr (congrArg Sum.inr he))
      | rfl

def childCoefficient (p : List Bool) (f : CircleL2) (b : Bool) : ℝ :=
  (if b then haarRight else haarLeft)
    (localAverage (p.length + 1) f (bottomLeaf p false))
    (localAverage (p.length + 1) f (bottomLeaf p true))

def childDifferential (p : List Bool) (f h : CircleL2) (b : Bool) : ℝ :=
  (if b then haarRightDifferential else haarLeftDifferential)
    (localAverage (p.length + 1) f (bottomLeaf p false))
    (localAverage (p.length + 1) f (bottomLeaf p true))
    (localAverage (p.length + 1) h (bottomLeaf p false))
    (localAverage (p.length + 1) h (bottomLeaf p true))

def childDerivativeTerm (p : List Bool) (f h : CircleL2) (b : Bool) : CircleL2 :=
  (Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ)) * childDifferential p f h b) •
    cellRestriction (p.length + 1) (bottomLeaf p b) f +
  (Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ)) * childCoefficient p f b) •
    cellRestriction (p.length + 1) (bottomLeaf p b) h

/-- The exact local product formula for the true Fréchet derivative on
the two actual periodic children. -/
theorem columnDifferential_two_children (p : List Bool) (f h : CircleL2)
    (hf : ∀ x, 0 < localAverage (p.length + 1) f x) :
    columnDifferential (some p) f h = childDerivativeTerm p f h false + childDerivativeTerm p f h true := by
  rw [columnDifferential_local_formula (some p) f h hf, nodeMode_some]
  dsimp only [nodeDepth]
  unfold fixedColumnDifferential
  have hs := bottom_sum (E := CircleL2) p
    (fun x : Grid (p.length + 1) => (
      (Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ)) *
        haarColumnDifferential (p.length + 1) (localAverage (p.length + 1) f)
          (localAverage (p.length + 1) h) (some (bottomDetail p)) x) • cellRestriction (p.length + 1) x f +
      (Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ)) *
        haarColumn (p.length + 1) (localAverage (p.length + 1) f) (some (bottomDetail p)) x) •
          cellRestriction (p.length + 1) x h)) (by
    intro x hl hr
    simp only [haarColumnDifferential, haarColumn,
      detailColumnDifferential_bottom_off p _ _ x hl hr, detailColumn_bottom_off p _ x hl hr,
      mul_zero, zero_smul, add_zero])
  convert hs using 1
  · apply Finset.sum_congr
    · ext x
      simp
    · intro x hx
      rfl
  · simp only [childDerivativeTerm, childCoefficient, childDifferential, Bool.false_eq_true,
      ↓reduceIte, haarColumnDifferential, haarColumn, detailColumnDifferential_bottom_left,
      detailColumnDifferential_bottom_right, detailColumn_bottom_left, detailColumn_bottom_right]

theorem childDerivativeTerm_ae (p : List Bool) (f h : CircleL2) (b : Bool) :
    childDerivativeTerm p f h b =ᵐ[haarAddCircle]
      (cellSet (p.length + 1) (bottomLeaf p b)).indicator (fun y =>
        (Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ)) * childDifferential p f h b : ℝ) • f y +
        (Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ)) * childCoefficient p f b : ℝ) • h y) := by
  filter_upwards [Lp.coeFn_add
      ((Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ)) * childDifferential p f h b) •
        cellRestriction (p.length + 1) (bottomLeaf p b) f)
      ((Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ)) * childCoefficient p f b) •
        cellRestriction (p.length + 1) (bottomLeaf p b) h),
      Lp.coeFn_smul (Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ)) * childDifferential p f h b)
        (cellRestriction (p.length + 1) (bottomLeaf p b) f),
      Lp.coeFn_smul (Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ)) * childCoefficient p f b)
        (cellRestriction (p.length + 1) (bottomLeaf p b) h),
      cellRestriction_ae (p.length + 1) (bottomLeaf p b) f,
      cellRestriction_ae (p.length + 1) (bottomLeaf p b) h] with y ha hd hc hf hh
  change _ = _ at ha
  rw [show childDerivativeTerm p f h b y = _ from ha]
  simp only [Pi.add_apply, hd, hc, Pi.smul_apply, hf, hh]
  by_cases hy : y ∈ cellSet (p.length + 1) (bottomLeaf p b)
  · simp only [Set.indicator_of_mem hy]
  · simp only [Set.indicator_of_notMem hy, smul_zero, add_zero]

theorem columnDifferential_supported (p : List Bool) (f h : CircleL2)
    (hf : ∀ x, 0 < localAverage (p.length + 1) f x) :
    ∀ᵐ y ∂haarAddCircle, y ∉ nodeCell p → columnDifferential (some p) f h y = 0 := by
  rw [columnDifferential_two_children p f h hf]
  filter_upwards [Lp.coeFn_add (childDerivativeTerm p f h false) (childDerivativeTerm p f h true),
    childDerivativeTerm_ae p f h false, childDerivativeTerm_ae p f h true] with y ha hl hr
  intro hy
  rw [ha]
  simp only [Pi.add_apply, hl, hr,
    Set.indicator_of_notMem (show y ∉ cellSet (p.length + 1) (bottomLeaf p false) from fun h => hy (Or.inl h)),
    Set.indicator_of_notMem (show y ∉ cellSet (p.length + 1) (bottomLeaf p true) from fun h => hy (Or.inr h)),
    add_zero]

end SHE.FiniteHaar
