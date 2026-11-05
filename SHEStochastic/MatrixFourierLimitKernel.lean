module

public import SHEStochastic.MatrixConditionalMildSolution
public import SHEStochastic.MatrixFourierLimitCharacteristics

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixFourierLimitKernel
open MeasureTheory ProbabilityTheory Filter SHE SHE.PredictableL2 MatrixInfiniteHaar MatrixFourierCoordinates
open scoped NNReal ENNReal Topology Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [mΩ : MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (Gn : ℕ → MatrixNonlinearCoefficient.Coefficient d) {Cn : ℕ → ℝ≥0} {β : ℝ≥0}
    (hGn : ∀ m,HolderWith (Cn m) β (Gn m).value) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (N : ℕ → FiniteScalarIto.Family F μ H (d×FiniteHaar.HaarNode))
    (U : ℕ → ℝ≥0×Ω → Physical (d := d)) (hU : ∀ m,StronglyMeasurable[F.predictable] (U m))
    (hcU : ∀ m ω,Continuous (fun t => U m (t,ω))) (ξ : Ω → Physical (d := d))
    (hEquation : ∀ m,MatrixFourierMildRealization.RandomEquation F μ H (Gn m) (hGn m) hβ hβ1 (U m) (hU m) (N m) ξ)
    (G : MatrixNonlinearCoefficient.Coefficient d) {C : ℝ≥0} (hG : HolderWith C β G.value)
    (B : ℝ≥0) (hBound : ∀ m,(Gn m).bound ≤ B)
    (error : ℕ → ℝ) (he : ∀ m,0 ≤ error m) (helim : Tendsto error atTop (𝓝 0))
    (happrox : ∀ m z,‖G.value z-(Gn m).value z‖ ≤ error m)
    (Q : ProbabilityMeasure (CanonicalContinuousStateDriver.Space (E := Physical (d := d)) (ι := d×FiniteHaar.HaarNode) H))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto ((CanonicalApproximationCompactness.varyingLaws F μ H
      (fun m t ω => U m (t,ω)) hcU N) ∘ φ) atTop (𝓝 Q))

include hG hEquation hBound he helim happrox hφ hlim in
/-- The actual matrix approximation limit supplies a Borel continuation
kernel whose conditional laws solve the native vector SPDE. No conditional
martingale, moment, representation or kernel estimate is an extra input. -/
theorem supports (hH : (H : ℝ) ≤ 1) (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hBrown : ∀ m (j : Fin m → d×FiniteHaar.HaarNode),FiniteBrownianLawOn
      (CanonicalStateDriverFiltration.filtration H) Q.toMeasure H
      (fun i => CanonicalStateDriverFiltration.coordinate H (j i)) (fun i k => if j i=j k then 1 else 0)) :
    MatrixConditionalMildSolution.Supports H Q.toMeasure G hH := by
  have hm (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ) := MatrixFourierLimitCharacteristics.linear
    F μ H Gn hGn hβ hβ1 N U hU hcU ξ hEquation B hBound Q φ hlim i a n hnull
  apply MatrixConditionalMildSolution.conditional H Q.toMeasure G hG hβ hβ1 hH hBrown
    (fun i a n => (hm i a n).1) (fun i a n t => ((hm i a n).2 t).memLp (4 : ℝ≥0))
  · intro i a n
    exact MatrixFourierLimitCharacteristics.square F μ H Gn hGn hβ hβ1 N U hU hcU ξ hEquation
      G hG B hBound error he helim happrox Q φ hφ hlim i a n hnull
  · intro i a n k
    exact MatrixFourierLimitCharacteristics.mixed F μ H Gn hGn hβ hβ1 N U hU hcU ξ hEquation
      G hG B hBound error he helim happrox Q φ hφ hlim i a n hnull k

include hG hEquation hBound he helim happrox hφ hlim in
/-- The same selected limiting law solves the Fourier equation before
conditioning as well. Retaining this conclusion avoids reconstructing
the mother solution from its conditional kernels when blocks are pasted. -/
theorem fourier (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hBrown : ∀ m (j : Fin m → d×FiniteHaar.HaarNode),FiniteBrownianLawOn
      (CanonicalStateDriverFiltration.filtration H) Q.toMeasure H
      (fun i => CanonicalStateDriverFiltration.coordinate H (j i)) (fun i k => if j i=j k then 1 else 0)) :
    MatrixFourierMildRealization.RandomEquation (CanonicalStateDriverFiltration.filtration H) Q.toMeasure H
      G hG hβ hβ1 (fun p => CanonicalStateDriverFiltration.state H p.1 p.2)
      (CanonicalStateDriverFiltration.state_predictable H)
      (MatrixCanonicalFourierRecognition.family H Q.toMeasure hBrown) (CanonicalStateDriverFiltration.state H 0) := by
  intro i a n t ht
  have hs := MatrixFourierLimitCharacteristics.equation F μ H Gn hGn hβ hβ1 N U hU hcU ξ hEquation
    G hG B hBound error he helim happrox Q φ hφ hlim i a n hnull hBrown t ht
  filter_upwards [hs] with x hx
  have h0 : x.1 (StoppedPathPasting.origin H)=CanonicalStateDriverFiltration.state H 0 x := by
    simp [CanonicalStateDriverFiltration.state,CanonicalStateDriverFiltration.clock,StoppedPathPasting.origin]
  dsimp only [CanonicalLinearFluctuation.value] at hx
  rw [min_eq_left ht,h0] at hx
  exact sub_eq_iff_eq_add'.mp hx

end SHEStochastic.MatrixFourierLimitKernel
