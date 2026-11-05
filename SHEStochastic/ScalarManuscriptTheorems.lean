module

public import SHEStochastic.ScalarTheoremOneOne
public import SHEStochastic.ScalarPhysicalFullLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarManuscriptTheorems
open MeasureTheory SHE SHE.DyadicApproximation AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- Manuscript Theorem 1.1, for every positive global Hölder exponent
and deterministic square-integrable initial datum. -/
theorem theorem_1_1 (T : ℝ≥0) (hT : 0<T)
    {g : ℝ→ℝ} {L β : ℝ≥0} (hg : HolderWith L β g) (hβ : 0<β)
    (B : ℝ≥0) (hB : ∀ z,‖g z‖≤B) (c : ℝ) (hc : 0<c) (hell : ∀ z,c≤|g z|)
    (u₀ : RealL2) :
    ∃! law,ScalarTheoremOneOne.Realizes T g u₀ law :=
  ScalarTheoremOneOne.theorem_1_1 T hT hg hβ B hB c hc hell u₀

/-- Manuscript Theorem 1.2(i), with Borel linear-growth drift and
deterministic L² initial state. -/
theorem theorem_1_2_i (T : ℝ≥0) (hT : 0<T)
    {g : ℝ→ℝ} {L β : ℝ≥0} (hg : HolderWith L β g) (hβ : 0<β)
    (B : ℝ≥0) (hB : ∀ z,‖g z‖≤B) (c : ℝ≥0) (hc : 0<c) (hell : ∀ z,(c : ℝ)≤|g z|)
    (b : ScalarLinearGrowthDriftField.Data T) (u₀ : RealL2) :
    ∃! law,ScalarPhysicalFullLaw.Realizes T g b u₀ law := by
  simpa only [ScalarPhysicalFullLaw.realizes_iff] using
    ScalarTheoremOneTwo.theorem_1_2_i T hT hg hβ B hB c hc hell b u₀

/-- Manuscript Theorem 1.2(ii), with no upper bound on the diffusion
and all global Hölder exponents in the stated range. -/
theorem theorem_1_2_ii (T : ℝ≥0) (hT : 0<T)
    {g : ℝ→ℝ} {L β : ℝ≥0} (hg : HolderWith L β g) (hβ : 0<β) (hβ₁ : β≤1)
    (c : ℝ≥0) (hc : 0<c) (hell : ∀ z,(c : ℝ)≤|g z|)
    (b : ScalarLinearGrowthDriftField.Data T) (u₀ : RealL2)
    (hInf : MemLp (u₀ : AddCircle (1 : ℝ) → ℝ) ⊤ haarAddCircle) :
    ∃! law,ScalarPhysicalFullLaw.Realizes T g b u₀ law := by
  simpa only [ScalarPhysicalFullLaw.realizes_iff] using
    ScalarTheoremOneTwo.theorem_1_2_ii T hT hg hβ hβ₁ c hc hell b u₀ hInf

/-- At the Lipschitz endpoint of Theorem 1.2(ii), the L² initial
condition already suffices. -/
theorem theorem_1_2_ii_lipschitz (T : ℝ≥0) (hT : 0<T)
    {g : ℝ→ℝ} {L : ℝ≥0} (hg : HolderWith L 1 g)
    (c : ℝ≥0) (hc : 0<c) (hell : ∀ z,(c : ℝ)≤|g z|)
    (b : ScalarLinearGrowthDriftField.Data T) (u₀ : RealL2) :
    ∃! law,ScalarPhysicalFullLaw.Realizes T g b u₀ law := by
  simpa only [ScalarPhysicalFullLaw.realizes_iff] using
    ScalarTheoremOneTwo.theorem_1_2_ii_lipschitz T hT hg c hc hell b u₀

end SHEStochastic.ScalarManuscriptTheorems
