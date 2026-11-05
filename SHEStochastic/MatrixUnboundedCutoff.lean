module

public import SHEStochastic.UnboundedCoefficientCutoff
public import SHEStochastic.MatrixClosedGlobalWeakExistence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixUnboundedCutoff
open MeasureTheory Matrix MatrixInfiniteHaar
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {n : ℕ} (G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β)
    (ell : ℝ) (hell : 0 < ell) (hLower : ∀ z,ell • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ G z*(G z)ᴴ)

/-- Radial state truncation preserves the original matrix ellipticity
and the exact Holder seminorm. Only the upper bound depends on radius. -/
def coefficient (R : ℝ≥0) : MatrixNonlinearCoefficient.Coefficient (Fin n) where
  value := UnboundedCoefficientCutoff.coefficient G R
  measurable := ((UnboundedCoefficientCutoff.holder hG R).continuous hβ).measurable
  bound := ⟨‖G 0‖+(C : ℝ)*(R : ℝ)^(β : ℝ),by positivity⟩
  norm_bound := UnboundedCoefficientCutoff.bounded hG R
  lower := ell
  lower_pos := hell
  lower_bound := UnboundedCoefficientCutoff.preserves
    (fun A => ell • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ A*Aᴴ) hLower R

theorem holder (R : ℝ≥0) :
    HolderWith C β (coefficient G hG hβ ell hell hLower R).value :=
  UnboundedCoefficientCutoff.holder hG R

theorem agrees (R : ℝ≥0) {z : EuclideanSpace ℝ (Fin n)} (hz : ‖z‖ ≤ R) :
    (coefficient G hG hβ ell hell hLower R).value z=G z :=
  UnboundedCoefficientCutoff.agrees G R hz

/-- This growth bound is uniform over all truncation radii, so later
nonexplosion estimates do not inherit the artificial upper cutoff. -/
theorem growth (R : ℝ≥0) (z : EuclideanSpace ℝ (Fin n)) :
    ‖(coefficient G hG hβ ell hell hLower R).value z‖ ≤
      (‖G 0‖+(C : ℝ))*(1+‖z‖^(β : ℝ)) :=
  UnboundedCoefficientCutoff.growth hG R z

local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩

/-- Every radius has a constructed global vector weak solution with
the prescribed random L2 initial law and original cutoff coefficient.
Passing these laws to an unbounded-coefficient solution remains separate. -/
theorem exists_solution (hβ1 : β ≤ 1) (R : ℝ≥0) (ρ₀ : MatrixLocalBlockChain.L2Law (n := n)) :
    ∃ S : MatrixGlobalWeakExistence.Solution 1 (coefficient G hG hβ ell hell hLower R)
      (holder G hG hβ ell hell hLower R) hβ hβ1 (by norm_num) ρ₀,
      Nonempty (MatrixGlobalOriginalFourier.Realization S) :=
  MatrixClosedGlobalWeakExistence.exists_solution (coefficient G hG hβ ell hell hLower R)
    (holder G hG hβ ell hell hLower R) hβ hβ1 ρ₀

end SHEStochastic.MatrixUnboundedCutoff
