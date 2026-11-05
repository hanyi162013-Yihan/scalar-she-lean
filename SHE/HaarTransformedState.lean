module

public import SHE.CellNegative

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.FiniteHaar
open Finset Set MeasureTheory AddCircle CircleHeat
open scoped ContDiff
local instance haarTransformedState_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def transformedState (p : List Bool) (T : CircleL2 →L[ℝ] E) : CircleL2 →L[ℝ] ColumnState E :=
  ((localAverageFunctional (p.length+1) (bottomLeaf p false)).prod
    (localAverageFunctional (p.length+1) (bottomLeaf p true))).prod
  (((Real.sqrt (((2^(p.length+1):ℕ):ℝ))) •
    (T.comp ((cellRestriction (p.length+1) (bottomLeaf p false)).restrictScalars ℝ))).prod
   ((Real.sqrt (((2^(p.length+1):ℕ):ℝ))) •
    (T.comp ((cellRestriction (p.length+1) (bottomLeaf p true)).restrictScalars ℝ))))

theorem transformedState_apply (p : List Bool) (T : CircleL2 →L[ℝ] E) (f : CircleL2) :
    transformedState p T f =
      ((localAverage (p.length+1) f (bottomLeaf p false),localAverage (p.length+1) f (bottomLeaf p true)),
        (Real.sqrt (((2^(p.length+1):ℕ):ℝ)) • T (cellRestriction (p.length+1) (bottomLeaf p false) f),
         Real.sqrt (((2^(p.length+1):ℕ):ℝ)) • T (cellRestriction (p.length+1) (bottomLeaf p true) f))) := rfl

/-- Every bounded real linear output transform can be moved into the
two physical numerator slots of the literal local Haar state. -/
theorem globalHaarColumn_transformed_state (p : List Bool) (T : CircleL2 →L[ℝ] E) (f : CircleL2) :
    T (globalHaarColumn (some p) f) = stateColumn (transformedState p T f) := by
  rw [globalHaarColumn_two_children,map_add,map_smul,map_smul,transformedState_apply]
  simp only [stateColumn,massCoefficient,Bool.false_eq_true,↓reduceIte,smul_smul,mul_comm]

/-- Genuine higher derivatives commute with the actual output operator
and retain the exact finite-dimensional two-child state description. -/
theorem globalHaarColumn_jet_transformed_state (p : List Bool) (T : CircleL2 →L[ℝ] E)
    (f : CircleL2) (hf : ∀ x, 0 < localAverage (p.length+1) f x) (j : ℕ) (v : Fin j → CircleL2) :
    T (iteratedFDeriv ℝ j (globalHaarColumn (some p)) f v) =
      iteratedFDeriv ℝ j stateColumn (transformedState p T f) (fun i => transformedState p T (v i)) := by
  have hp : transformedState p T f ∈ statePositive := ⟨hf _,hf _⟩
  have he := (transformedState p T).iteratedFDerivWithin_comp_right
    (fun z hz => (contDiffAt_stateColumn z hz ∞).contDiffWithinAt)
    isOpen_statePositive.uniqueDiffOn (isOpen_statePositive.preimage (transformedState p T).continuous).uniqueDiffOn
    hp (i := j) (by simp : (j : WithTop ℕ∞) ≤ ∞)
  have hfun : stateColumn ∘ transformedState p T = T ∘ globalHaarColumn (some p) :=
    funext (fun f => (globalHaarColumn_transformed_state p T f).symm)
  have hleft := T.iteratedFDeriv_comp_left (contDiffAt_globalHaarColumn (some p) f hf j) (i := j) le_rfl
  rw [hfun,iteratedFDerivWithin_eq_iteratedFDeriv
      (isOpen_statePositive.preimage (transformedState p T).continuous).uniqueDiffOn
      (T.contDiff.contDiffAt.comp f (contDiffAt_globalHaarColumn (some p) f hf j)) hp,
    iteratedFDerivWithin_eq_iteratedFDeriv isOpen_statePositive.uniqueDiffOn
      (contDiffAt_stateColumn (transformedState p T f) hp j) hp] at he
  rw [hleft] at he
  exact congrArg (fun A => A v) he

end SHE.FiniteHaar
