module

public import SHEStochastic.MatrixGlobalOriginalFourier
public import SHEStochastic.CanonicalBrownianFamily

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
noncomputable section

namespace SHEStochastic.MatrixClosedGlobalWeakExistence
open MeasureTheory SHE SHE.FiniteHaar MatrixInfiniteHaar
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩

/-- Closed global weak existence for the bounded uniformly elliptic
Holder matrix coefficient and every random L2 initial law. The continuous
predictable state and its original-coefficient Brownian driver are both
constructed, starting from the canonical Gaussian probability measure.
No probability space or Brownian family is an input hypothesis. -/
theorem exists_solution (G : MatrixNonlinearCoefficient.Coefficient (Fin n)) {C β : ℝ≥0}
    (hG : HolderWith C β G.value) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (ρ₀ : MatrixLocalBlockChain.L2Law (n := n)) :
    ∃ S : MatrixGlobalWeakExistence.Solution 1 G hG hβ hβ1 (by norm_num) ρ₀,
      Nonempty (MatrixGlobalOriginalFourier.Realization S) :=
  MatrixGlobalOriginalFourier.exists_solution CanonicalBrownianFamily.filtration CanonicalBrownianFamily.measure
    1 G hG hβ hβ1 le_rfl (by norm_num) (CanonicalBrownianFamily.haar n) ρ₀

end SHEStochastic.MatrixClosedGlobalWeakExistence
