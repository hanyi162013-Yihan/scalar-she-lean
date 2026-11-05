module

public import SHEStochastic.MatrixGlobalWeakExistence
public import SHEStochastic.CompletedMatrixFourierSolution
public import SHEStochastic.MatrixFourierCovarianceCongruence
public import SHEStochastic.MatrixSmoothApproximationInputs
public import SHEStochastic.NativeGlobalPredictableRotation
public import SHEStochastic.MatrixFiniteHorizonMildRecognition
public import SHEStochastic.MatrixFourierHorizonRestriction

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
noncomputable section

namespace SHEStochastic.MatrixGlobalOriginalFourier
open MeasureTheory SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := Fin n)) := borel _
local instance : BorelSpace (Input (d := Fin n)) := ⟨rfl⟩
variable {H : ℝ≥0} {G : MatrixNonlinearCoefficient.Coefficient (Fin n)} {C β : ℝ≥0}
    {hG : HolderWith C β G.value} {hβ : 0<β} {hβ1 : β ≤ 1} {hH0 : 0<H}
    {ρ₀ : MatrixLocalBlockChain.L2Law (n := n)} (S : MatrixGlobalWeakExistence.Solution H G hG hβ hβ1 hH0 ρ₀)
local notation "ρ" => (Measure.dirac () : Measure Unit)
local notation "Fc" => RandomInitialBrownianFamily.filtration ρ S.law.toMeasure (MatrixBlockNaturalFiltration.filtration H)
local notation "μc" => IndependentNoiseCompletion.measure ρ S.law.toMeasure
local instance (priority := 2000) completedSigma :
    MeasurableSpace (RandomInitialBrownianFamily.Space ρ S.law.toMeasure) :=
  @NullMeasurableSpace.instMeasurableSpace (Unit×MatrixGlobalBlockPath.Space (n := n) H)
    inferInstance ((ρ).prod S.law.toMeasure)

/-- The completed global state keeps the very same continuous path. -/
def state : ℝ≥0×RandomInitialBrownianFamily.Space ρ S.law.toMeasure → Physical (d := Fin n) :=
  CompletedMatrixFourierSolution.state S.law.toMeasure MatrixGlobalFourierStep.state

theorem predictable : StronglyMeasurable[(Fc).predictable] (state S) :=
  CompletedMatrixFourierSolution.predictable (MatrixBlockNaturalFiltration.filtration H) S.law.toMeasure
    MatrixGlobalFourierStep.state (MatrixGlobalFourierStep.predictable hH0)

/-- Every finite union of blocks has the original, literal diffusion
coefficient on the same completed global state space. The construction
here does not yet assert coherence between the selected noise families. -/
theorem exists_family (M : ℕ) :
    ∃ B : FiniteScalarIto.Family Fc μc ((M : ℝ≥0)*H) (Fin n×HaarNode),
      MatrixFourierMildRealization.RandomEquation Fc μc ((M : ℝ≥0)*H) G hG hβ hβ1
        (state S) (predictable S) B ((MatrixGlobalBlockPath.state H 0) ∘ Prod.snd) := by
  let T : ℝ≥0 := (M : ℝ≥0)*H
  let P := RandomInitialBrownianFamily.family ρ S.law.toMeasure (MatrixBlockNaturalFiltration.filtration H) T (S.family T)
  have he := MatrixFourierPullback.equation (Ξ := RandomInitialBrownianFamily.Space ρ S.law.toMeasure)
    (D := Fc) Prod.snd (IndependentNoiseCompletion.snd_preserving ρ S.law.toMeasure)
    (CompletedMatrixFourierSolution.filtered (MatrixBlockNaturalFiltration.filtration H) S.law.toMeasure)
    (MatrixSmoothCoefficient.coefficient G 0) (MatrixBoundedContinuationKernel.target_holder G hG) hβ hβ1
    MatrixGlobalFourierStep.state (MatrixGlobalFourierStep.predictable hH0) (S.family T) P
    (fun _ _ _ => rfl) (MatrixGlobalBlockPath.state H 0) (S.equation M)
  have hβr : 0<(β : ℝ) := by exact_mod_cast hβ
  have hnorm (z w : EuclideanSpace ℝ (Fin n)) : ‖G.value z-G.value w‖ ≤ (C : ℝ)*‖z-w‖^(β : ℝ) := by
    simpa only [dist_eq_norm] using hG.dist_le z w
  have hc (z : EuclideanSpace ℝ (Fin n)) : G.covariance z=(MatrixSmoothCoefficient.coefficient G 0).covariance z := by
    symm
    exact MatrixSmoothApproximationInputs.covariance_eq G C.coe_nonneg hβr hnorm z
  exact MatrixFourierCovarianceCongruence.exists_family Fc G (MatrixSmoothCoefficient.coefficient G 0) hc
    (state S) (predictable S) μc T hG hβ hβ1 (MatrixBoundedContinuationKernel.target_holder G hG) hβ hβ1
    P (RandomInitialBrownianFamily.contains_null ρ S.law.toMeasure (MatrixBlockNaturalFiltration.filtration H))
    ((MatrixGlobalBlockPath.state H 0) ∘ Prod.snd) he

/-- A coherent canonical solution admits one global original-square
Brownian driver on the same completed global state space. The same
family works for every finite union of blocks. -/
theorem exists_coherent_family (hS : ∀ T K,(S.family T).W=(S.family K).W) :
    ∃ B : ∀ T : ℝ≥0,FiniteScalarIto.Family Fc μc T (Fin n×HaarNode),
      (∀ T K,(B T).W=(B K).W) ∧
      ∀ M : ℕ,MatrixFourierMildRealization.RandomEquation Fc μc ((M : ℝ≥0)*H) G hG hβ hβ1
        (state S) (predictable S) (B ((M : ℝ≥0)*H)) ((MatrixGlobalBlockPath.state H 0) ∘ Prod.snd) := by
  let P := fun T => RandomInitialBrownianFamily.family ρ S.law.toMeasure
    (MatrixBlockNaturalFiltration.filtration H) T (S.family T)
  have hP (T K : ℝ≥0) (i : Fin n×HaarNode) (t : ℝ≥0) (_ht : t ≤  min T K) :
      (P T).W i t =ᵐ[μc] (P K).W i t := by
    apply Filter.Eventually.of_forall
    intro ω
    change (S.family T).W i t ω.2=(S.family K).W i t ω.2
    rw [hS T K]
  have hβr : 0<(β : ℝ) := by exact_mod_cast hβ
  have hnorm (z w : EuclideanSpace ℝ (Fin n)) : ‖G.value z-G.value w‖ ≤ (C : ℝ)*‖z-w‖^(β : ℝ) := by
    simpa only [dist_eq_norm] using hG.dist_le z w
  have hc (z : EuclideanSpace ℝ (Fin n)) : G.covariance z=(MatrixSmoothCoefficient.coefficient G 0).covariance z :=
    (MatrixSmoothApproximationInputs.covariance_eq G C.coe_nonneg hβr hnorm z).symm
  obtain ⟨B,hBc,hB⟩ := NativeGlobalPredictableRotation.exists_family P hP
    MatrixPredictableHaarRotation.basis MatrixPredictableHaarRotation.basis
    (MatrixEqualCovarianceRotation.rotation Fc G (MatrixSmoothCoefficient.coefficient G 0) hc (state S) (predictable S))
    (MatrixEqualCovarianceRotation.measurable Fc G (MatrixSmoothCoefficient.coefficient G 0) hc (state S) (predictable S))
    (RandomInitialBrownianFamily.contains_null ρ S.law.toMeasure (MatrixBlockNaturalFiltration.filtration H))
  refine ⟨B,hBc,?_⟩
  intro M
  let T : ℝ≥0 := (M : ℝ≥0)*H
  have he := MatrixFourierPullback.equation (Ξ := RandomInitialBrownianFamily.Space ρ S.law.toMeasure)
    (D := Fc) Prod.snd (IndependentNoiseCompletion.snd_preserving ρ S.law.toMeasure)
    (CompletedMatrixFourierSolution.filtered (MatrixBlockNaturalFiltration.filtration H) S.law.toMeasure)
    (MatrixSmoothCoefficient.coefficient G 0) (MatrixBoundedContinuationKernel.target_holder G hG) hβ hβ1
    MatrixGlobalFourierStep.state (MatrixGlobalFourierStep.predictable hH0) (S.family T) (P T)
    (fun _ _ _ => rfl) (MatrixGlobalBlockPath.state H 0) (S.equation M)
  change MatrixFourierMildRealization.RandomEquation Fc μc T (MatrixSmoothCoefficient.coefficient G 0)
    (MatrixBoundedContinuationKernel.target_holder G hG) hβ hβ1 (state S) (predictable S) (P T)
    ((MatrixGlobalBlockPath.state H 0) ∘ Prod.snd) at he
  intro i a n t ht
  have hh := hB T (StoppedItoInputs.stop Fc μc T t (MatrixFourierInput.input Fc μc T G hG hβ hβ1 (state S) (predictable S) i a n))
  rw [MatrixFourierCovarianceCongruence.stop_commutes Fc G (MatrixSmoothCoefficient.coefficient G 0) hc (state S) (predictable S) μc T t _,
    MatrixFourierCovarianceCongruence.input_eq Fc G (MatrixSmoothCoefficient.coefficient G 0) hc (state S) (predictable S) μc T
      hG hβ hβ1 (MatrixBoundedContinuationKernel.target_holder G hG) hβ hβ1 i a n] at hh
  have hs := he i a n t ht
  rw [←hh] at hs
  exact hs

/-- The original diffusion is realized by one coherent global Brownian
family on the completed global state space. -/
structure Realization where
  family : ∀ T : ℝ≥0,FiniteScalarIto.Family Fc μc T (Fin n×HaarNode)
  coherent : ∀ T K,(family T).W=(family K).W
  equation : ∀ M : ℕ,MatrixFourierMildRealization.RandomEquation Fc μc ((M : ℝ≥0)*H) G hG hβ hβ1
    (state S) (predictable S) (family ((M : ℝ≥0)*H)) ((MatrixGlobalBlockPath.state H 0) ∘ Prod.snd)

theorem exists_realization (hS : ∀ T K,(S.family T).W=(S.family K).W) : Nonempty (Realization S) := by
  obtain ⟨B,hB,he⟩ := exists_coherent_family S hS
  exact ⟨⟨B,hB,he⟩⟩

/-- The original coefficient also satisfies the Hilbert mild equation
on every block union within the existing analytic heat horizon. -/
theorem Realization.mild (R : Realization S) (M : ℕ) (hMH : (((M : ℝ≥0)*H : ℝ≥0) : ℝ) ≤ 1) :
    MatrixFourierMildRecognition.Equation Fc μc ((M : ℝ≥0)*H) G (state S) (predictable S) hMH
      (R.family ((M : ℝ≥0)*H)) ((MatrixGlobalBlockPath.state H 0) ∘ Prod.snd) :=
  MatrixFourierMildRecognition.equation Fc μc _ G hG hβ hβ1 (state S) (predictable S) hMH _ _ (R.equation M)

/-- The same original-square driver satisfies the native equation on
every finite horizon, including horizons ending inside a block. -/
theorem Realization.equation_all (R : Realization S) (T : ℝ≥0) :
    MatrixFourierMildRealization.RandomEquation Fc μc T G hG hβ hβ1 (state S) (predictable S)
      (R.family T) ((MatrixGlobalBlockPath.state H 0) ∘ Prod.snd) := by
  let M : ℕ := ⌈T/H⌉₊+1
  have hTM : T ≤ (M : ℝ≥0)*H := CountablePathConcatenation.covering H T hH0
  exact MatrixFourierHorizonRestriction.equation Fc μc hTM G hG hβ hβ1 (state S) (predictable S)
    (R.family ((M : ℝ≥0)*H)) (R.family T)
    (fun i t _ => Filter.Eventually.of_forall (fun ω => congrFun (congrFun (congrFun (R.coherent T ((M : ℝ≥0)*H)) i) t) ω))
    ((MatrixGlobalBlockPath.state H 0) ∘ Prod.snd) (R.equation M)

/-- The constructed continuous global state is the genuine original
matrix weak mild solution at every finite time. Both the finite-time
convolution and its original-square Brownian driver are constructed. -/
theorem Realization.mild_all (R : Realization S) (T : ℝ≥0) :
    MatrixFiniteHorizonMildRecognition.Equation Fc μc T G (state S) (predictable S) (R.family T)
      ((MatrixGlobalBlockPath.state H 0) ∘ Prod.snd) :=
  MatrixFiniteHorizonMildRecognition.equation Fc μc T G hG hβ hβ1 (state S) (predictable S) _ _ (R.equation_all S T)

theorem initial_law : (μc).map (fun ω => state S (0,ω))=ρ₀.val.toMeasure := by
  have hp := IndependentNoiseCompletion.snd_preserving ρ S.law.toMeasure
  have hm : Measurable (MatrixGlobalBlockPath.state (n := n) H 0) :=
    (MatrixGlobalBlockPath.measurable H).comp (measurable_const.prodMk measurable_id)
  let π : RandomInitialBrownianFamily.Space ρ S.law.toMeasure → MatrixGlobalBlockPath.Space (n := n) H := Prod.snd
  change (μc).map (MatrixGlobalBlockPath.state H 0 ∘ π)=ρ₀.val.toMeasure
  rw [←Measure.map_map hm hp.measurable,hp.map_eq]
  exact S.initial

theorem moments (t : ℝ≥0) : MemLp (fun ω => state S (t,ω)) 2 μc :=
  (S.moments t).comp_measurePreserving (IndependentNoiseCompletion.snd_preserving ρ S.law.toMeasure)

theorem continuous (ω : RandomInitialBrownianFamily.Space ρ S.law.toMeasure) :
    Continuous (fun t => state S (t,ω)) := MatrixGlobalBlockPath.continuous H hH0 ω.2

/-- Bounded uniformly elliptic Holder matrix diffusion has a global
continuous predictable solution with the prescribed random L2 initial
law and one original-square Brownian driver. Its Fourier equation
holds on every finite union of blocks. -/
theorem exists_solution {Ω : Type*} [MeasurableSpace Ω]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ℝ≥0) (G : MatrixNonlinearCoefficient.Coefficient (Fin n)) {C β : ℝ≥0}
    (hG : HolderWith C β G.value) (hβ : 0<β) (hβ1 : β ≤ 1) (hH : (H : ℝ) ≤ 1) (hH0 : 0<H)
    (N : FiniteScalarIto.Family F μ H (Fin n×HaarNode)) (ρ₀ : MatrixLocalBlockChain.L2Law (n := n)) :
    ∃ S : MatrixGlobalWeakExistence.Solution H G hG hβ hβ1 hH0 ρ₀,Nonempty (Realization S) := by
  obtain ⟨S,hS⟩ := MatrixGlobalWeakExistence.exists_coherent_solution F μ H G hG hβ hβ1 hH hH0 N ρ₀
  exact ⟨S,exists_realization S hS⟩

end SHEStochastic.MatrixGlobalOriginalFourier
