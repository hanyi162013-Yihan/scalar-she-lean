module

public import SHEStochastic.MatrixGlobalOriginalFourier

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
noncomputable section

namespace SHEStochastic.MatrixGlobalHaarRestriction
open MeasureTheory SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
variable {H : ℝ≥0} {G : MatrixNonlinearCoefficient.Coefficient (Fin n)} {C β : ℝ≥0}
    {hG : HolderWith C β G.value} {hβ : 0<β} {hβ1 : β≤1} {hH0 : 0<H}
    {ρ₀ : MatrixLocalBlockChain.L2Law (n := n)}
    (S : MatrixGlobalWeakExistence.Solution H G hG hβ hβ1 hH0 ρ₀)
local notation "ρ" => (Measure.dirac () : Measure Unit)
local notation "Fc" => RandomInitialBrownianFamily.filtration ρ S.law.toMeasure (MatrixBlockNaturalFiltration.filtration H)
local notation "μc" => IndependentNoiseCompletion.measure ρ S.law.toMeasure
local instance (priority := 2000) completedSigma :
    MeasurableSpace (RandomInitialBrownianFamily.Space ρ S.law.toMeasure) :=
  @NullMeasurableSpace.instMeasurableSpace (Unit×MatrixGlobalBlockPath.Space (n := n) H)
    inferInstance ((ρ).prod S.law.toMeasure)

abbrev Space := RandomInitialBrownianFamily.Space ρ S.law.toMeasure
abbrev filtration := Fc
abbrev measure := μc

/-- The constructed solution viewed in continuous L2 path space. -/
def path (T : ℝ≥0) : Space S → StoppedPathPasting.Path T (Physical (d := Fin n)) :=
  NativeContinuousPath.path T (fun t ω => MatrixGlobalOriginalFourier.state S (t,ω))
    (MatrixGlobalOriginalFourier.continuous S)

theorem path_measurable (T : ℝ≥0) : Measurable (path S T) :=
  NativeContinuousPath.measurable_path T (fun t ω => MatrixGlobalOriginalFourier.state S (t,ω))
    (MatrixGlobalOriginalFourier.continuous S)
    ((MatrixGlobalOriginalFourier.predictable S).mono (predictable_le_product Fc)).measurable

/-- No new law is assumed: this is the path law of the constructed solution. -/
def law (T : ℝ≥0) : ProbabilityMeasure (StoppedPathPasting.Path T (Physical (d := Fin n))) :=
  ⟨(μc).map (path S T),inferInstance⟩

theorem initial_path_law (T : ℝ≥0) :
    (law S T).toMeasure.map (fun p => p (StoppedPathPasting.origin T))=ρ₀.val.toMeasure := by
  have he : (fun p : StoppedPathPasting.Path T (Physical (d := Fin n)) =>
      p (StoppedPathPasting.origin T)) ∘ path S T=
      (fun ω => MatrixGlobalOriginalFourier.state S (0,ω)) := by
    funext ω
    change MatrixGlobalOriginalFourier.state S ((0 : ℝ).toNNReal,ω)=_
    rw [Real.toNNReal_zero]
  change ((μc).map (path S T)).map (fun p => p (StoppedPathPasting.origin T))=_
  rw [Measure.map_map (continuous_eval_const _).measurable (path_measurable S T),he]
  exact MatrixGlobalOriginalFourier.initial_law S

/-- Restrict the constructed global original-coefficient solution to a
short horizon and realize its genuine covariance-adapted infinite Haar
mild equation. This changes neither the state nor its initial law. -/
theorem exists_family (R : MatrixGlobalOriginalFourier.Realization S)
    (T : ℝ≥0) (hT : (T : ℝ)≤1) :
    ∃ B : FiniteScalarIto.Family Fc μc T (Fin n×HaarNode),
      MatrixRandomMildExistence.Equation G hT B (MatrixGlobalOriginalFourier.state S)
        (MatrixGlobalOriginalFourier.predictable S) ((MatrixGlobalBlockPath.state H 0) ∘ Prod.snd) :=
  MatrixFourierMildRecognition.exists_haar_equation Fc μc T G hG hβ hβ1
    (MatrixGlobalOriginalFourier.state S) (MatrixGlobalOriginalFourier.predictable S) hT (R.family T)
    ((MatrixGlobalBlockPath.state H 0) ∘ Prod.snd) (R.equation_all S T)
    (RandomInitialBrownianFamily.contains_null ρ S.law.toMeasure (MatrixBlockNaturalFiltration.filtration H))

end SHEStochastic.MatrixGlobalHaarRestriction
