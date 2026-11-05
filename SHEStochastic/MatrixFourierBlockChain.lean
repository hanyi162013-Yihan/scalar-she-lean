module

public import SHEStochastic.MatrixLocalBlockChain

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixFourierBlockChain
open MeasureTheory ProbabilityTheory SHE SHE.FiniteHaar MatrixInfiniteHaar
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩

/-- The existing continuation chain with the unconditional local
Fourier equations retained from the very same selected laws. -/
structure Data (H : ℝ≥0) (G : MatrixNonlinearCoefficient.Coefficient (Fin n)) {C β : ℝ≥0}
    (hG : HolderWith C β G.value) (hβ : 0<β) (hβ1 : β≤1) (hH : (H : ℝ)≤1) where
  base : MatrixLocalBlockChain.Data H (MatrixSmoothCoefficient.coefficient G 0) hH
  brownian : ∀ ρ,MatrixBoundedContinuationKernel.Brownian H (base.select ρ).law
  fourier : ∀ ρ,MatrixBoundedContinuationKernel.FourierSolution H G hG hβ hβ1 (base.select ρ).law (brownian ρ)

theorem exists_data {Ω : Type*} [MeasurableSpace Ω]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ℝ≥0) (G : MatrixNonlinearCoefficient.Coefficient (Fin n)) {C β : ℝ≥0}
    (hG : HolderWith C β G.value) (hβ : 0<β) (hβ1 : β≤1) (hH : (H : ℝ)≤1) (hH0 : 0<H)
    (N : FiniteScalarIto.Family F μ H (Fin n×HaarNode)) : Nonempty (Data H G hG hβ hβ1 hH) := by
  classical
  let e := fun ρ : MatrixLocalBlockChain.L2Law (n := n) =>
    MatrixBoundedContinuationKernel.exists_restartable_with_fourier F μ H G hG hβ hβ1 hH hH0 N ρ.val ρ.property
  let Q := fun ρ => Classical.choose (e ρ)
  let B := fun ρ => Classical.choose (Classical.choose_spec (e ρ))
  have hp (ρ) := Classical.choose_spec (Classical.choose_spec (e ρ))
  let base : MatrixLocalBlockChain.Data H (MatrixSmoothCoefficient.coefficient G 0) hH :=
    ⟨fun ρ => ⟨Q ρ,(hp ρ).1,(hp ρ).2.1,(hp ρ).2.2.2⟩,fun ρ => by
      filter_upwards [(hp ρ).2.1] with z hz
      exact ⟨hz.choose,trivial⟩⟩
  exact ⟨⟨base,B,fun ρ => (hp ρ).2.2.1⟩⟩

variable {H : ℝ≥0} {G : MatrixNonlinearCoefficient.Coefficient (Fin n)} {C β : ℝ≥0}
    {hG : HolderWith C β G.value} {hβ : 0<β} {hβ1 : β≤1} {hH : (H : ℝ)≤1}
    (D : Data H G hG hβ hβ1 hH) (ρ₀ : MatrixLocalBlockChain.L2Law (n := n))

theorem block_brownian (j : ℕ) : MatrixBoundedContinuationKernel.Brownian H (D.base.blockLaw ρ₀ j) :=
  D.brownian (D.base.initialLaws ρ₀ j)

theorem block_fourier (j : ℕ) : MatrixBoundedContinuationKernel.FourierSolution H G hG hβ hβ1
    (D.base.blockLaw ρ₀ j) (block_brownian D ρ₀ j) := D.fourier (D.base.initialLaws ρ₀ j)

end SHEStochastic.MatrixFourierBlockChain
