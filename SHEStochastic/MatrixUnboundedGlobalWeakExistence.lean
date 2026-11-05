module

public import SHEStochastic.MatrixUnboundedGlobalBlocks
public import SHEStochastic.MatrixGlobalWeakExistence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
noncomputable section

namespace SHEStochastic.MatrixUnboundedGlobalWeakExistence
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar Matrix
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := Fin n)) := borel _
local instance : BorelSpace (Input (d := Fin n)) := ⟨rfl⟩
variable (G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ) {C β : ℝ≥0}
    (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β<1)
    (ρ₀ : MatrixLocalBlockChain.L2Law (n := n))

/-- A single global continuous vector state and coherent original
Brownian driver, with the unbounded Fourier equation on every unit
block in the shifted FULL global filtration. Thus every physical time
belongs to an actual equation window on the same probability space. -/
structure Solution where
  law : ProbabilityMeasure (MatrixGlobalBlockPath.Space (n := n) 1)
  initial : law.toMeasure.map (MatrixGlobalBlockPath.state 1 0)=ρ₀.val.toMeasure
  moments : ∀ t,MemLp (MatrixGlobalBlockPath.state 1 t) 2 law.toMeasure
  family : ∀ T : ℝ≥0,FiniteScalarIto.Family (MatrixBlockNaturalFiltration.filtration 1)
    law.toMeasure T (Fin n×HaarNode)
  coherent : ∀ T K,(family T).W=(family K).W
  blocks : ∀ k : ℕ,FiniteScalarIto.Family
    (DeterministicItoShift.filtration (MatrixBlockNaturalFiltration.filtration 1) ((k : ℝ≥0)*1))
    law.toMeasure 1 (Fin n×HaarNode)
  driver : ∀ (k : ℕ) (i : Fin n×HaarNode) (t : ℝ≥0),t≤1 → ∀ p,
    (blocks k).W i t p=(family (k+1)).W i ((k : ℝ≥0)+t) p-(family (k+1)).W i k p
  energy : ∀ k,Integrable
    (fun p => ‖MatrixGlobalBlockFourier.state (H := 1) zero_lt_one k p‖^2)
      (energyMeasure law.toMeasure 1)
  pathEnergy : ∀ k,Integrable
    (fun p : MatrixGlobalBlockPath.Space (n := n) 1 => ‖(p k).1‖^2) law.toMeasure
  blockState : ∀ᵐ p ∂law.toMeasure,∀ (k : ℕ) (s : ℝ≥0),s≤1 →
    MatrixGlobalBlockPath.state 1 ((k : ℝ≥0)+s) p=
      MatrixLocalBlockChain.state 1 s (p k)
  equation : ∀ k,MatrixUnboundedFourierPullback.Equation G hG hβ hβ1.le
    (MatrixGlobalBlockFourier.state zero_lt_one k) (MatrixGlobalBlockFourier.predictable zero_lt_one k)
    (energy k) (blocks k)
    (CanonicalStateDriverFiltration.state 1 0 ∘ MatrixGlobalBlockBundle.bundle 1 zero_lt_one k)

theorem continuous (_S : Solution G hG hβ hβ1 ρ₀) (p : MatrixGlobalBlockPath.Space (n := n) 1) :
    Continuous (fun t => MatrixGlobalBlockPath.state 1 t p) :=
  MatrixGlobalBlockPath.continuous 1 zero_lt_one p

theorem predictable (_S : Solution G hG hβ hβ1 ρ₀) :
    StronglyMeasurable[(MatrixBlockNaturalFiltration.filtration (n := n) 1).predictable]
      (fun p => MatrixGlobalBlockPath.state 1 p.1 p.2) :=
  MatrixBlockProcessAdapted.state_predictable 1 zero_lt_one

/-- The verified equation windows cover all nonnegative physical time. -/
theorem covering (t : ℝ≥0) : ∃ k : ℕ,∃ s : ℝ≥0,s≤1 ∧ (k : ℝ≥0)+s=t := by
  simpa only [mul_one] using CountablePathConcatenation.exists_block (1 : ℝ≥0) zero_lt_one t

variable (ell : ℝ) (hell : 0<ell)
    (hLower : ∀ z,ell • (1 : Matrix (Fin n) (Fin n) ℝ)≤G z*(G z)ᴴ)

include hell hLower in
/-- Global weak existence for a sublinear Holder matrix diffusion
and every random L2 initial law. Every selected block, matching endpoint,
full-past Brownian property and native equation is constructed. -/
theorem exists_solution : Nonempty (Solution G hG hβ hβ1 ρ₀) := by
  obtain ⟨D⟩ := MatrixUnboundedBlockChain.exists_data G hG hβ hβ1 1 ell hell hLower
    (by norm_num) zero_lt_one
  refine ⟨⟨⟨D.law ρ₀,inferInstance⟩,MatrixGlobalWeakExistence.initial_law D ρ₀ zero_lt_one,
    MatrixGlobalBlockPath.memLp D ρ₀ zero_lt_one,
    MatrixGlobalBrownianPast.family D ρ₀ zero_lt_one,(fun _ _ => rfl),
    MatrixGlobalBlockFamily.family D ρ₀ zero_lt_one,?_,
    MatrixUnboundedGlobalBlocks.blockEnergy D ρ₀ zero_lt_one,
    MatrixUnboundedGlobalBlocks.pathEnergy D ρ₀,
    (by
      change ∀ᵐ p ∂D.law ρ₀,∀ (k : ℕ) (s : ℝ≥0),s≤1 →
        MatrixGlobalBlockPath.state 1 ((k : ℝ≥0)+s) p=
          MatrixLocalBlockChain.state 1 s (p k)
      simpa only [mul_one] using MatrixGlobalBlockPath.block D ρ₀ zero_lt_one),
    MatrixUnboundedGlobalBlocks.equation D ρ₀ zero_lt_one⟩⟩
  intro k i t ht p
  change CanonicalStateDriverFiltration.coordinate 1 i t
    (MatrixGlobalBlockBundle.bundle 1 zero_lt_one k p)=
      MatrixGlobalBlockPath.driver 1 i ((k : ℝ≥0)+t) p-MatrixGlobalBlockPath.driver 1 i k p
  simpa only [MatrixGlobalBlockBundle.bundle,mul_one] using CanonicalStateDriverFiltration.coordinate_bundle 1
    (MatrixGlobalBlockPath.state 1) (MatrixGlobalBlockPath.continuous 1 zero_lt_one)
    (MatrixGlobalBlockPath.driver 1) (MatrixGlobalBlockPath.driver_continuous 1 zero_lt_one)
    (k : ℝ≥0) t ht i p

end SHEStochastic.MatrixUnboundedGlobalWeakExistence
