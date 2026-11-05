module

public import SHEStochastic.MatrixUnboundedFourierHorizonRestriction

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.MatrixUnboundedGlobalFourierAll
open MeasureTheory SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar Matrix
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := Fin n)) := borel _
local instance : BorelSpace (Input (d := Fin n)) := ⟨rfl⟩
variable {G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ} {C β : ℝ≥0}
    {hG : HolderWith C β G} {hβ : 0<β} {hβ1 : β<1}
    {ρ₀ : MatrixLocalBlockChain.L2Law (n := n)}
    (S : MatrixUnboundedGlobalWeakExistence.Solution G hG hβ hβ1 ρ₀)

/-- The globally pasted weak solution satisfies its ORIGINAL
unbounded matrix Fourier equation on every finite physical horizon,
with one coherent Brownian family and one state-dependent input. -/
theorem equation (T : ℝ≥0) :
    MatrixUnboundedFourierPullback.Equation G hG hβ hβ1.le
      (MatrixUnboundedGlobalFourierStep.state (n := n))
      (MatrixUnboundedGlobalFourierStep.predictable (n := n))
      (MatrixUnboundedGlobalEnergy.finite_energy S T)
      (S.family T) (MatrixGlobalBlockPath.state 1 0) := by
  obtain ⟨M,hM⟩ := exists_nat_gt (T : ℝ)
  have hTM : T ≤ (M : ℝ≥0) := by exact_mod_cast hM.le
  apply MatrixUnboundedFourierHorizonRestriction.equation
    (MatrixBlockNaturalFiltration.filtration 1) S.law.toMeasure hTM
    G hG hβ hβ1.le
    (MatrixUnboundedGlobalFourierStep.state (n := n))
    (MatrixUnboundedGlobalFourierStep.predictable (n := n))
    (MatrixUnboundedGlobalEnergy.finite_energy S (M : ℝ≥0))
    (MatrixUnboundedGlobalEnergy.finite_energy S T)
    (S.family (M : ℝ≥0)) (S.family T)
  · intro i t ht
    exact Filter.Eventually.of_forall (fun ω =>
      congrFun (congrFun (congrFun (S.coherent T (M : ℝ≥0)) i) t) ω)
  · exact MatrixUnboundedGlobalFourierEquation.equation S M

/-- A global unbounded vector weak solution with the full original
Fourier stochastic equation on every finite horizon. -/
structure FullSolution (G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β<1)
    (ρ₀ : MatrixLocalBlockChain.L2Law (n := n)) where
  base : MatrixUnboundedGlobalWeakExistence.Solution G hG hβ hβ1 ρ₀
  fullEquation : ∀ T, MatrixUnboundedFourierPullback.Equation G hG hβ hβ1.le
    (MatrixUnboundedGlobalFourierStep.state (n := n))
    (MatrixUnboundedGlobalFourierStep.predictable (n := n))
    (MatrixUnboundedGlobalEnergy.finite_energy base T)
    (base.family T) (MatrixGlobalBlockPath.state 1 0)

theorem exists_full_solution
    (G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β<1)
    (ρ₀ : MatrixLocalBlockChain.L2Law (n := n))
    (ell : ℝ) (hell : 0<ell)
    (hLower : ∀ z,ell • (1 : Matrix (Fin n) (Fin n) ℝ)≤G z*(G z)ᴴ) :
    Nonempty (FullSolution G hG hβ hβ1 ρ₀) := by
  obtain ⟨S⟩ := MatrixUnboundedGlobalWeakExistence.exists_solution
    G hG hβ hβ1 ρ₀ ell hell hLower
  exact ⟨⟨S, equation S⟩⟩

/-- Deterministic initial data are a special case of the random L2-law
construction; no separate existence theorem is needed for them. -/
def pointLaw (u₀ : Physical (d := Fin n)) : MatrixLocalBlockChain.L2Law (n := n) :=
  ⟨⟨Measure.dirac u₀, inferInstance⟩, memLp_dirac (by simp)⟩

theorem exists_deterministic_full_solution
    (G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β<1)
    (u₀ : Physical (d := Fin n)) (ell : ℝ) (hell : 0<ell)
    (hLower : ∀ z,ell • (1 : Matrix (Fin n) (Fin n) ℝ)≤G z*(G z)ᴴ) :
    Nonempty (FullSolution G hG hβ hβ1 (pointLaw u₀)) :=
  exists_full_solution G hG hβ hβ1 (pointLaw u₀) ell hell hLower

end SHEStochastic.MatrixUnboundedGlobalFourierAll
