module

public import SHE.HaarStateJets

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.FiniteHaar
open Finset MeasureTheory AddCircle CircleHeat Set
open scoped ContDiff
local instance haarNormalizedState_periodPos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def localAverageFunctional (n : ℕ) (x : Grid n) : CircleL2 →L[ℝ] ℝ :=
  (((2 ^ n : ℕ) : ℝ)) •
    (Complex.reCLM.comp ((innerSL ℂ (cellIndicator n x)).restrictScalars ℝ))

@[simp] theorem localAverageFunctional_apply (n : ℕ) (x : Grid n) (h : CircleL2) :
    localAverageFunctional n x h = localAverage n h x := rfl

/-- The literal two child averages and the child physical restrictions,
normalized so bounded directions have a depth-independent state norm. -/
def normalizedState (p : List Bool) : CircleL2 →L[ℝ] ColumnState CircleL2 :=
  ((localAverageFunctional (p.length + 1) (bottomLeaf p false)).prod
    (localAverageFunctional (p.length + 1) (bottomLeaf p true))).prod
  (((Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ))) •
      ((cellRestriction (p.length + 1) (bottomLeaf p false)).restrictScalars ℝ)).prod
    ((Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ))) •
      ((cellRestriction (p.length + 1) (bottomLeaf p true)).restrictScalars ℝ)))

theorem normalizedState_apply (p : List Bool) (f : CircleL2) : normalizedState p f =
    ((localAverage (p.length + 1) f (bottomLeaf p false),
      localAverage (p.length + 1) f (bottomLeaf p true)),
    (Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ)) • cellRestriction (p.length + 1) (bottomLeaf p false) f,
      Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ)) • cellRestriction (p.length + 1) (bottomLeaf p true) f)) := rfl

def localRestrictionNorm (p : List Bool) (h : CircleL2) : ℝ :=
  ‖cellRestriction (p.length + 1) (bottomLeaf p false) h‖ +
    ‖cellRestriction (p.length + 1) (bottomLeaf p true) h‖

theorem localRestrictionNorm_nonneg (p : List Bool) (h : CircleL2) : 0 ≤ localRestrictionNorm p h :=
  add_nonneg (norm_nonneg _) (norm_nonneg _)

theorem normalizedState_local_bound (p : List Bool) (h : CircleL2) :
    ‖normalizedState p h‖ ≤ Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ)) * localRestrictionNorm p h := by
  have hL : ‖cellRestriction (p.length + 1) (bottomLeaf p false) h‖ ≤ localRestrictionNorm p h :=
    le_add_of_nonneg_right (norm_nonneg _)
  have hR : ‖cellRestriction (p.length + 1) (bottomLeaf p true) h‖ ≤ localRestrictionNorm p h :=
    le_add_of_nonneg_left (norm_nonneg _)
  rw [normalizedState_apply, Prod.norm_def, Prod.norm_def, Prod.norm_def]
  apply max_le
  · apply max_le
    · exact (localAverage_cell_bound _ _ h).trans (mul_le_mul_of_nonneg_left hL (Real.sqrt_nonneg _))
    · exact (localAverage_cell_bound _ _ h).trans (mul_le_mul_of_nonneg_left hR (Real.sqrt_nonneg _))
  · apply max_le
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_left hL (Real.sqrt_nonneg _)
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_left hR (Real.sqrt_nonneg _)

theorem normalizedState_bounded_bound (p : List Bool) (h : CircleL2) (M : ℝ) (hM : 0 ≤ M)
    (hh : ∀ᵐ y ∂haarAddCircle, ‖h y‖ ≤ M) : ‖normalizedState p h‖ ≤ M := by
  have hchild (b : Bool) :
      ‖Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ)) •
        cellRestriction (p.length + 1) (bottomLeaf p b) h‖ ≤ M := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (cellRestriction_bounded_norm _ _ h M hM hh) (Real.sqrt_nonneg _)).trans_eq (by
      have hs : Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ)) ≠ 0 := by positivity
      field_simp)
  rw [normalizedState_apply, Prod.norm_def, Prod.norm_def, Prod.norm_def]
  exact max_le (max_le (localAverage_bounded_abs _ _ h M hM hh) (localAverage_bounded_abs _ _ h M hM hh))
    (max_le (hchild false) (hchild true))

theorem normalizedState_elliptic (p : List Bool) (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) :
    (normalizedState p f).1 ∈ massRectangle m U ∧ ‖(normalizedState p f).2‖ ≤ U := by
  constructor
  · exact ⟨⟨(localAverage_bounds_ae _ f m U hf _).1, (localAverage_bounds_ae _ f m U hf _).1⟩,
      ⟨(localAverage_bounds_ae _ f m U hf _).2, (localAverage_bounds_ae _ f m U hf _).2⟩⟩
  · exact (norm_snd_le (normalizedState p f)).trans
      (normalizedState_bounded_bound p f U (elliptic_upper_nonneg f m U hm hf)
        (CircleMultiplier.elliptic_norm_bound f m U hm hfreal hf))

theorem globalHaarColumn_state (p : List Bool) (f : CircleL2) :
    globalHaarColumn (some p) f = stateColumn (normalizedState p f) := by
  rw [globalHaarColumn_two_children, normalizedState_apply]
  simp only [stateColumn, massCoefficient, Bool.false_eq_true, ↓reduceIte, smul_smul, mul_comm]

theorem globalHaarColumn_jet_state (p : List Bool) (f : CircleL2)
    (hf : ∀ x, 0 < localAverage (p.length + 1) f x) (j : ℕ) (v : Fin j → CircleL2) :
    iteratedFDeriv ℝ j (globalHaarColumn (some p)) f v =
      iteratedFDeriv ℝ j stateColumn (normalizedState p f) (fun i => normalizedState p (v i)) := by
  have hp : normalizedState p f ∈ statePositive := ⟨hf _, hf _⟩
  have he := (normalizedState p).iteratedFDerivWithin_comp_right
    (fun z hz => (contDiffAt_stateColumn z hz ∞).contDiffWithinAt)
    isOpen_statePositive.uniqueDiffOn (isOpen_statePositive.preimage (normalizedState p).continuous).uniqueDiffOn
    hp (i := j) (by simp : (j : WithTop ℕ∞) ≤ ∞)
  have hfun : stateColumn ∘ normalizedState p = globalHaarColumn (some p) :=
    funext (fun f => (globalHaarColumn_state p f).symm)
  rw [hfun, iteratedFDerivWithin_eq_iteratedFDeriv
      (isOpen_statePositive.preimage (normalizedState p).continuous).uniqueDiffOn
      (contDiffAt_globalHaarColumn (some p) f hf j) hp,
    iteratedFDerivWithin_eq_iteratedFDeriv isOpen_statePositive.uniqueDiffOn
      (contDiffAt_stateColumn (normalizedState p f) hp j) hp] at he
  exact congrArg (fun A => A v) he

/-- Quantitative higher physical column estimate, localized to its two
children, with all nondistinguished directions bounded in `L∞`.
The genuine iterated Fréchet derivative is used on the left. -/
theorem globalHaarColumn_jet_one_slot (p : List Bool) (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (j : ℕ) (v : Fin (j + 1) → CircleL2) (M : Fin (j + 1) → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hv : ∀ i, i ≠ 0 → ∀ᵐ y ∂haarAddCircle, ‖v i y‖ ≤ M i) :
    ‖iteratedFDeriv ℝ (j + 1) (globalHaarColumn (some p)) f v‖ ≤
      stateJetBound m U hm (j + 1) *
        (Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ)) * localRestrictionNorm p (v 0)) *
          ∏ i ∈ univ.erase (0 : Fin (j + 1)), M i := by
  have hpos (x : Grid (p.length + 1)) : 0 < localAverage (p.length + 1) f x :=
    hm.trans_le (localAverage_bounds_ae _ f m U hf x).1
  rw [globalHaarColumn_jet_state p f hpos]
  have hb := normalizedState_elliptic p f m U hm hfreal hf
  have hn := (iteratedFDeriv ℝ (j + 1) stateColumn (normalizedState p f)).le_opNorm
    (fun i => normalizedState p (v i))
  have hs := hn.trans (mul_le_mul_of_nonneg_right (stateColumn_jet_bound m U hm (j + 1) _ hb.1 hb.2)
    (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
  rw [← Finset.mul_prod_erase univ _ (mem_univ (0 : Fin (j + 1)))] at hs
  apply hs.trans
  have hprod : (∏ i ∈ univ.erase (0 : Fin (j + 1)), ‖normalizedState p (v i)‖) ≤
      ∏ i ∈ univ.erase (0 : Fin (j + 1)), M i :=
    prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i hi => normalizedState_bounded_bound p (v i) (M i) (hM i)
      (hv i (mem_erase.mp hi).1))
  have hmul := mul_le_mul (normalizedState_local_bound p (v 0)) hprod (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
    (mul_nonneg (Real.sqrt_nonneg _) (localRestrictionNorm_nonneg p _))
  exact (mul_le_mul_of_nonneg_left hmul (stateJetBound_nonneg m U hm (j + 1))).trans_eq (by ring)

end SHE.FiniteHaar
