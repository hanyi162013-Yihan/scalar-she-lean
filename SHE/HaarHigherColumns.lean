module

public import SHE.HaarNormalizedState

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.FiniteHaar
open Finset MeasureTheory AddCircle CircleHeat Set
open scoped ContDiff
local instance haarHigherColumns_periodPos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem cellRestriction_idempotent (n : ℕ) (x : Grid n) (f : CircleL2) :
    cellRestriction n x (cellRestriction n x f) = cellRestriction n x f := by
  apply Lp.ext
  filter_upwards [cellRestriction_ae n x (cellRestriction n x f), cellRestriction_ae n x f] with y ho hi
  rw [ho]
  by_cases hy : y ∈ cellSet n x
  · rw [Set.indicator_of_mem hy]
  · rw [Set.indicator_of_notMem hy, hi, Set.indicator_of_notMem hy]

theorem sum_cellRestriction (n : ℕ) (f : CircleL2) : (∑ x : Grid n, cellRestriction n x f) = f := by
  have hc : ∀ᵐ y ∂haarAddCircle, ∀ x : Grid n,
      cellRestriction n x f y = (cellSet n x).indicator f y :=
    ae_all_iff.mpr (fun x => cellRestriction_ae n x f)
  apply Lp.ext
  filter_upwards [Lp.coeFn_fun_finsetSum univ (fun x : Grid n => cellRestriction n x f), hc] with y hs hc
  rw [hs]
  rw [sum_eq_single ((gridCellEquiv n).symm (cellIndex n y))]
  · rw [hc]
    exact Set.indicator_of_mem (by change cellIndex n y = _; rw [Equiv.apply_symm_apply]) f
  · intro x hx hne
    rw [hc]
    apply Set.indicator_of_notMem
    intro hy
    apply hne
    exact ((gridCellEquiv n).symm_apply_apply x).symm.trans (congrArg (gridCellEquiv n).symm hy.symm)
  · simp

theorem sum_cellRestriction_norm_sq (n : ℕ) (f : CircleL2) :
    (∑ x : Grid n, ‖cellRestriction n x f‖ ^ 2) = ‖f‖ ^ 2 := by
  calc
    _ = ∑ x : Grid n, (inner ℂ f (cellRestriction n x f)).re := by
      apply sum_congr rfl
      intro x hx
      have he : inner ℂ f (cellRestriction n x f) =
          inner ℂ (cellRestriction n x f) (cellRestriction n x f) := by
        rw [← cellRestriction_inner, cellRestriction_idempotent]
      rw [he]
      exact InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (cellRestriction n x f)
    _ = (inner ℂ f (∑ x : Grid n, cellRestriction n x f)).re := by rw [inner_sum, Complex.re_sum]
    _ = ‖f‖ ^ 2 := by rw [sum_cellRestriction]; exact (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) f).symm

def nodeRestriction (p : List Bool) : CircleL2 →L[ℂ] CircleL2 :=
  cellRestriction (p.length+1) (bottomLeaf p false) + cellRestriction (p.length+1) (bottomLeaf p true)

theorem nodeRestriction_ae (p : List Bool) (f : CircleL2) :
    nodeRestriction p f =ᵐ[haarAddCircle] (nodeCell p).indicator f := by
  filter_upwards [Lp.coeFn_add (cellRestriction (p.length+1) (bottomLeaf p false) f)
      (cellRestriction (p.length+1) (bottomLeaf p true) f),
    cellRestriction_ae (p.length+1) (bottomLeaf p false) f,
    cellRestriction_ae (p.length+1) (bottomLeaf p true) f] with y ha hl hr
  change (cellRestriction (p.length+1) (bottomLeaf p false) f +
    cellRestriction (p.length+1) (bottomLeaf p true) f) y = _
  rw [ha]
  simp only [Pi.add_apply, hl, hr]
  have hd := Set.disjoint_left.mp (cellSet_disjoint (p.length+1) _ _ (bottomLeaf_ne p))
  by_cases hyl : y ∈ cellSet (p.length+1) (bottomLeaf p false)
  · have hyr : y ∉ cellSet (p.length+1) (bottomLeaf p true) := fun h => hd hyl h
    simp only [Set.indicator_of_mem hyl, Set.indicator_of_notMem hyr,
      Set.indicator_of_mem (show y ∈ nodeCell p from Or.inl hyl), add_zero]
  · by_cases hyr : y ∈ cellSet (p.length+1) (bottomLeaf p true)
    · simp only [Set.indicator_of_notMem hyl, Set.indicator_of_mem hyr,
        Set.indicator_of_mem (show y ∈ nodeCell p from Or.inr hyr), zero_add]
    · simp only [Set.indicator_of_notMem hyl, Set.indicator_of_notMem hyr,
        Set.indicator_of_notMem (show y ∉ nodeCell p from fun h => h.elim hyl hyr), add_zero]

theorem nodeRestriction_globalHaarColumn (p : List Bool) (f : CircleL2) :
    nodeRestriction p (globalHaarColumn (some p) f) = globalHaarColumn (some p) f := by
  apply Lp.ext
  filter_upwards [nodeRestriction_ae p (globalHaarColumn (some p) f), globalHaarColumn_supported p f] with y hr hs
  rw [hr]
  by_cases hy : y ∈ nodeCell p
  · rw [Set.indicator_of_mem hy]
  · rw [Set.indicator_of_notMem hy, hs hy]

/-- All genuine higher derivative columns retain the literal dyadic
support, at every order and for arbitrary physical `L²` directions. -/
theorem globalHaarColumn_jet_supported (p : List Bool) (f : CircleL2)
    (hf : ∀ x, 0 < localAverage (p.length + 1) f x) (j : ℕ) (v : Fin j → CircleL2) :
    ∀ᵐ y ∂haarAddCircle, y ∉ nodeCell p → iteratedFDeriv ℝ j (globalHaarColumn (some p)) f v y = 0 := by
  have he := ((nodeRestriction p).restrictScalars ℝ).iteratedFDeriv_comp_left
    (contDiffAt_globalHaarColumn (some p) f hf j) (i := j) le_rfl
  have hfun : ((nodeRestriction p).restrictScalars ℝ) ∘ globalHaarColumn (some p) = globalHaarColumn (some p) :=
    funext (nodeRestriction_globalHaarColumn p)
  rw [hfun] at he
  have hid := congrArg (fun A => A v) he
  change iteratedFDeriv ℝ j (globalHaarColumn (some p)) f v = nodeRestriction p
    (iteratedFDeriv ℝ j (globalHaarColumn (some p)) f v) at hid
  filter_upwards [nodeRestriction_ae p (iteratedFDeriv ℝ j (globalHaarColumn (some p)) f v)] with y hy
  intro hny
  rw [hid, hy, Set.indicator_of_notMem hny]

def leafPath : (n : ℕ) → Grid n → List Bool
  | 0, _ => []
  | n+1, Sum.inl x => false :: leafPath n x
  | n+1, Sum.inr x => true :: leafPath n x

theorem leafPath_length (n : ℕ) (x : Grid n) : (leafPath n x).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => cases x <;> simp only [leafPath, List.length_cons, ih]

theorem leafPath_injective (n : ℕ) : Function.Injective (leafPath n) := by
  induction n with
  | zero => intro x y h; cases x; cases y; rfl
  | succ n ih =>
    intro x y h
    cases x <;> cases y
    all_goals simp only [leafPath, List.cons.injEq] at h
    · exact congrArg Sum.inl (ih h.2)
    · simp at h
    · simp at h
    · exact congrArg Sum.inr (ih h.2)

theorem leafPath_child_eval {E : Type*} (F : ∀ n, Grid n → E) (n : ℕ) (x : Grid n) (b : Bool) :
    F ((leafPath n x).length + 1) (bottomLeaf (leafPath n x) b) = F (n+1) (leafChild n x b) := by
  induction n generalizing F with
  | zero => cases x; cases b <;> rfl
  | succ n ih =>
    cases x with
    | inl x => exact ih (fun k y => F (k+1) (Sum.inl y)) x
    | inr x => exact ih (fun k y => F (k+1) (Sum.inr y)) x

theorem localRestrictionNorm_leafPath (n : ℕ) (x : Grid n) (h : CircleL2) :
    localRestrictionNorm (leafPath n x) h = ‖cellRestriction (n+1) (leafChild n x false) h‖ +
      ‖cellRestriction (n+1) (leafChild n x true) h‖ := by
  unfold localRestrictionNorm
  rw [leafPath_child_eval (fun k y => ‖cellRestriction k y h‖) n x false,
    leafPath_child_eval (fun k y => ‖cellRestriction k y h‖) n x true]

theorem sum_localRestrictionNorm_sq (n : ℕ) (h : CircleL2) :
    (∑ x : Grid n, (localRestrictionNorm (leafPath n x) h) ^ 2) ≤ 2 * ‖h‖ ^ 2 := by
  calc
    _ ≤ ∑ x : Grid n, 2 * (‖cellRestriction (n+1) (leafChild n x false) h‖ ^ 2 +
        ‖cellRestriction (n+1) (leafChild n x true) h‖ ^ 2) := by
      apply sum_le_sum
      intro x hx
      rw [localRestrictionNorm_leafPath]
      nlinarith [sq_nonneg (‖cellRestriction (n+1) (leafChild n x false) h‖ -
        ‖cellRestriction (n+1) (leafChild n x true) h‖)]
    _ = 2 * ∑ y : Grid (n+1), ‖cellRestriction (n+1) y h‖ ^ 2 := by
      rw [sum_leafChildren n, mul_sum]
    _ = _ := by erw [sum_cellRestriction_norm_sq]

/-- The actual generation square sum for all higher derivative columns:
the one-slot `L²` input costs exactly the inverse interval length.
The common constant is independent of generation and approximation. -/
theorem globalHaarColumn_jet_generation_L2 (n : ℕ) (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (j : ℕ) (v : Fin (j + 1) → CircleL2) (M : Fin (j + 1) → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hv : ∀ i, i ≠ 0 → ∀ᵐ y ∂haarAddCircle, ‖v i y‖ ≤ M i) :
    (∑ x : Grid n, ‖iteratedFDeriv ℝ (j + 1) (globalHaarColumn (some (leafPath n x))) f v‖ ^ 2) ≤
      2 * (stateJetBound m U hm (j + 1)) ^ 2 * (((2 ^ (n+1) : ℕ) : ℝ)) * ‖v 0‖ ^ 2 *
        (∏ i ∈ univ.erase (0 : Fin (j + 1)), M i) ^ 2 := by
  let C := (stateJetBound m U hm (j + 1)) ^ 2 * (((2 ^ (n+1) : ℕ) : ℝ)) *
    (∏ i ∈ univ.erase (0 : Fin (j + 1)), M i) ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ ≤ ∑ x : Grid n, C * localRestrictionNorm (leafPath n x) (v 0) ^ 2 := by
      apply sum_le_sum
      intro x hx
      have hh := pow_le_pow_left₀ (norm_nonneg _)
        (globalHaarColumn_jet_one_slot (leafPath n x) f m U hm hfreal hf j v M hM hv) 2
      rw [leafPath_length] at hh
      apply hh.trans_eq
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
      dsimp only [C]
      ring
    _ = C * ∑ x : Grid n, localRestrictionNorm (leafPath n x) (v 0) ^ 2 := (mul_sum _ _ _).symm
    _ ≤ C * (2 * ‖v 0‖ ^ 2) := mul_le_mul_of_nonneg_left (sum_localRestrictionNorm_sq n (v 0)) hC
    _ = _ := by dsimp only [C]; ring

end SHE.FiniteHaar
