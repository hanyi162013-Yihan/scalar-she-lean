module

public import SHEStochastic.MatrixDyadicCoherence
public import SHEStochastic.MatrixDyadicPairing

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.MatrixGlobalHaarGram
open MeasureTheory Matrix SHE SHE.FiniteHaar MatrixDyadicCoherence
open scoped NNReal MatrixOrder Matrix.Norms.L2Operator

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))

/-- All actual countable weighted Haar blocks are mutually orthogonal,
including arbitrary nested/disjoint nodes and all state components. -/
theorem weighted_gram (κ : AddCircle (1 : ℝ) → Matrix d d ℝ)
    (hκ : Measurable κ) (hInt : Integrable κ μ) (B : ℝ≥0)
    (hB : ∀ᵐ x ∂μ, ‖κ x‖ ≤ B) (m : ℝ) (hm : 0 < m)
    (hLo : ∀ᵐ x ∂μ, m • (1 : Matrix d d ℝ) ≤ κ x)
    (q r : HaarNode) (i j : d) :
    inner ℝ (MatrixGlobalHaar.column κ q i)
      (MatrixFieldOperator.operator κ hκ B hB (MatrixGlobalHaar.column κ r j))=
        if (i,q)=(j,r) then 1 else 0 := by
  let n := max (nodeDepth q) (nodeDepth r)
  have hq : nodeDepth q ≤ n := le_max_left _ _
  have hr : nodeDepth r ≤ n := le_max_right _ _
  let A := MatrixFiniteHaar.haarColumn n (MatrixDyadicMass.profile κ n) (nodeMode n q hq)
  let D := MatrixFiniteHaar.haarColumn n (MatrixDyadicMass.profile κ n) (nodeMode n r hr)
  have hint := MatrixDyadicPairing.integrable_cross n κ hInt A D
  have hh := (MatrixHaarPairings.entry i j).integral_comp_comm hint
  have hGram := MatrixFiniteHaar.haar_gram n (MatrixDyadicMass.profile κ n)
    (MatrixDyadicMass.positive κ hInt m hm hLo n) (nodeMode n q hq) (nodeMode n r hr)
  have hmode : nodeMode n q hq=nodeMode n r hr ↔ q=r := by
    constructor
    · intro h
      simpa only [modePath_nodeMode] using congrArg (modePath n) h
    · rintro rfl
      rfl
  rw [L2.inner_def]
  calc
    _ = ∫ x, MatrixDyadicPairing.cross n κ A D x i j ∂μ := by
      apply integral_congr_ae
      filter_upwards [column_ae κ q i, column_ae κ r j,
        coefficient_grid κ hInt n q hq, coefficient_grid κ hInt n r hr,
        BoundedFieldOperator.operator_ae (MatrixFieldOperator.field κ hκ B hB)
          (MatrixGlobalHaar.column κ r j)] with x hqi hrj hcq hcr hop
      change inner ℝ (MatrixGlobalHaar.column κ q i x)
        (BoundedFieldOperator.operator (MatrixFieldOperator.field κ hκ B hB)
          (MatrixGlobalHaar.column κ r j) x)=
        ((A (MatrixDyadicPairing.leaf n x))ᴴ*κ x*D (MatrixDyadicPairing.leaf n x)) i j
      rw [hqi, hop, hrj]
      change inner ℝ (MatrixHaarRootColumns.column (coefficient κ q x) i)
        (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (κ x)
          (MatrixHaarRootColumns.column (coefficient κ r x) j))=_
      rw [MatrixHaarRootColumns.inner_columns, hcq, hcr]
      rfl
    _ = (∫ x, MatrixDyadicPairing.cross n κ A D x ∂μ) i j := hh
    _ = _ := by
      rw [MatrixDyadicPairing.integral_cross n κ hInt, hGram]
      by_cases hqr : q=r <;> by_cases hij : i=j
      all_goals simp [hmode, hqr, hij, Matrix.one_apply, Prod.mk.injEq]

end SHEStochastic.MatrixGlobalHaarGram
