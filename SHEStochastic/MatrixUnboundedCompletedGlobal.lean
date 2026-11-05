module

public import SHEStochastic.MatrixUnboundedDeterministicMild
public import SHEStochastic.CompletedMatrixFourierSolution
public import SHEStochastic.RandomInitialBrownianFamily

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixUnboundedCompletedGlobal
open MeasureTheory SHE SHE.PredictableL2 MatrixInfiniteHaar
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
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

local notation "ρ" => (Measure.dirac () : Measure Unit)
local notation "Fc" => RandomInitialBrownianFamily.filtration ρ S.law.toMeasure
    (MatrixBlockNaturalFiltration.filtration 1)
local notation "μc" => IndependentNoiseCompletion.measure ρ S.law.toMeasure
local instance (priority := 2000) completedSigma :
    MeasurableSpace (RandomInitialBrownianFamily.Space ρ S.law.toMeasure) :=
  @NullMeasurableSpace.instMeasurableSpace (Unit×MatrixGlobalBlockPath.Space (n := n) 1)
    inferInstance ((ρ).prod S.law.toMeasure)

def state : ℝ≥0×RandomInitialBrownianFamily.Space ρ S.law.toMeasure → Physical (d := Fin n) :=
  CompletedMatrixFourierSolution.state S.law.toMeasure MatrixUnboundedGlobalFourierStep.state

theorem predictable : StronglyMeasurable[(Fc).predictable] (state S) :=
  CompletedMatrixFourierSolution.predictable (MatrixBlockNaturalFiltration.filtration 1) S.law.toMeasure
    MatrixUnboundedGlobalFourierStep.state MatrixUnboundedGlobalFourierStep.predictable

theorem contains_null : NullCompleteFiltration.ContainsNullSets (Fc) (μc) :=
  RandomInitialBrownianFamily.contains_null ρ S.law.toMeasure (MatrixBlockNaturalFiltration.filtration 1)

def family (T : ℝ≥0) : FiniteScalarIto.Family (Fc) (μc) T (Fin n×FiniteHaar.HaarNode) :=
  RandomInitialBrownianFamily.family ρ S.law.toMeasure (MatrixBlockNaturalFiltration.filtration 1)
    T (S.family T)

theorem coherent (T K : ℝ≥0) : (family S T).W=(family S K).W := by
  funext i t z
  exact congrFun (congrFun (congrFun (S.coherent T K) i) t) z.2

/-- The completed probability space retains the original UNBOUNDED
matrix Fourier equation with the same global state and Brownian family. -/
theorem equation (T : ℝ≥0) :
    MatrixUnboundedFourierPullback.Equation G hG hβ hβ1.le
      (state S) (predictable S)
      (MatrixUnboundedFourierPullback.energy
        (Ξ := RandomInitialBrownianFamily.Space ρ S.law.toMeasure) (mΞ := completedSigma S) Prod.snd
        (IndependentNoiseCompletion.snd_preserving ρ S.law.toMeasure)
        MatrixUnboundedGlobalFourierStep.state (MatrixUnboundedGlobalEnergy.finite_energy S T))
      (family S T) ((MatrixGlobalBlockPath.state 1 0) ∘ Prod.snd) := by
  exact MatrixUnboundedFourierPullback.equation
    (Ξ := RandomInitialBrownianFamily.Space ρ S.law.toMeasure) (mΞ := completedSigma S)
    (D := Fc) (ν := μc) Prod.snd
    (IndependentNoiseCompletion.snd_preserving ρ S.law.toMeasure)
    (CompletedMatrixFourierSolution.filtered (MatrixBlockNaturalFiltration.filtration 1) S.law.toMeasure)
    G hG hβ hβ1.le
    MatrixUnboundedGlobalFourierStep.state MatrixUnboundedGlobalFourierStep.predictable
    (MatrixUnboundedGlobalEnergy.finite_energy S T)
    (S.family T) (family S T) (fun _ _ _ => rfl)
    (MatrixGlobalBlockPath.state 1 0)
    (MatrixUnboundedGlobalFourierAll.equation S T)

end SHEStochastic.MatrixUnboundedCompletedGlobal
