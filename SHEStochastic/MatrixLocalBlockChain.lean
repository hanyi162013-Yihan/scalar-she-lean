module

public import SHEStochastic.MatrixBoundedContinuationKernel
public import SHEStochastic.MatrixCanonicalBlockChain

@[expose] public section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixLocalBlockChain
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩

abbrev Block (H : ℝ≥0) (G : MatrixNonlinearCoefficient.Coefficient (Fin n)) (hH : (H : ℝ)≤1)
    (ρ : L2Law (n := n)) := MatrixCanonicalBlockChain.Block H
      (fun Q => MatrixConditionalMildSolution.Supports H Q.toMeasure G hH) ρ

abbrev Data (H : ℝ≥0) (G : MatrixNonlinearCoefficient.Coefficient (Fin n)) (hH : (H : ℝ)≤1) :=
  MatrixCanonicalBlockChain.Data H (fun Q => MatrixConditionalMildSolution.Supports H Q.toMeasure G hH)

theorem exists_data {Ω : Type*} [MeasurableSpace Ω]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ℝ≥0) (G : MatrixNonlinearCoefficient.Coefficient (Fin n)) {C β : ℝ≥0}
    (hG : HolderWith C β G.value) (hβ : 0<β) (hβ1 : β≤1) (hH : (H : ℝ)≤1) (hH0 : 0<H)
    (N : FiniteScalarIto.Family F μ H (Fin n×HaarNode)) :
    Nonempty (Data H (MatrixSmoothCoefficient.coefficient G 0) hH) := by
  classical
  let e := fun ρ : L2Law (n := n) => MatrixBoundedContinuationKernel.exists_restartable_kernel
    F μ H G hG hβ hβ1 hH hH0 N ρ.val ρ.property
  exact ⟨⟨fun ρ => ⟨Classical.choose (e ρ),(Classical.choose_spec (e ρ)).1,
    (Classical.choose_spec (e ρ)).2.1,(Classical.choose_spec (e ρ)).2.2⟩,fun ρ => by
      filter_upwards [(Classical.choose_spec (e ρ)).2.1] with z hz
      exact ⟨hz.choose,trivial⟩⟩⟩

end SHEStochastic.MatrixLocalBlockChain
