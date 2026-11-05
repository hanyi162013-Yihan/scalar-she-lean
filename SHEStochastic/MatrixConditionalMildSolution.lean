module

public import SHEStochastic.MatrixFourierDisintegration
public import SHEStochastic.MatrixFourierMildRecognition
public import SHEStochastic.QuadraticMomentBounds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixConditionalMildSolution
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar
open CanonicalStateDriverFiltration
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d : Type*} [Fintype d] [DecidableEq d]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
variable (H : ℝ≥0) (Q : Measure (CanonicalContinuousStateDriver.Space
    (E := Physical (d := d)) (ι := d×HaarNode) H)) [IsProbabilityMeasure Q]
    (G : MatrixNonlinearCoefficient.Coefficient d) {C β : ℝ≥0}
    (hG : HolderWith C β G.value) (hβ : 0 < β) (hβ1 : β ≤ 1)
local notation "M" => (fun i a n => CanonicalLinearFluctuation.value (ι := d×HaarNode) H
  (MatrixFourierCoordinates.coordinate i a n) ((n : ℝ)^2))

/-- A genuine conditional solution kernel, required only almost
everywhere for the initial law reached by the original construction. -/
def Supports (hH : (H : ℝ) ≤ 1) : Prop :=
  ∀ᵐ z ∂CanonicalInitialKernel.initialLaw H Q,
    ∃ hBrown : ∀ m (j : Fin m → d×HaarNode),FiniteBrownianLawOn (filtration H)
      (CanonicalInitialKernel.kernel H Q z) H (fun l => coordinate H (j l))
      (fun l k => if j l=j k then 1 else 0),
    MatrixFourierMildRecognition.Equation (filtration H) (CanonicalInitialKernel.kernel H Q z) H G
      (fun p => state H p.1 p.2) (state_predictable H) hH
      (MatrixCanonicalFourierRecognition.family H (CanonicalInitialKernel.kernel H Q z) hBrown) (state H 0)

/-- Linear, square and mixed characteristics of the constructed joint
law give actual vector mild solutions under its initial-state kernel.
Brownian motion is retained in the whole canonical past. -/
theorem conditional (hH : (H : ℝ) ≤ 1)
    (hBrown : ∀ m (j : Fin m → d×HaarNode),FiniteBrownianLawOn (filtration H) Q H
      (fun l => coordinate H (j l)) (fun l k => if j l=j k then 1 else 0))
    (hM : ∀ i a n,Martingale (M i a n) (filtration H) Q)
    (hM4 : ∀ i a n t,MemLp (M i a n t) 4 Q)
    (hSquare : ∀ i a n,Martingale (MatrixFourierDisintegration.square H G hG hβ hβ1 i a n) (filtration H) Q)
    (hMixed : ∀ i a n k,Martingale
      (MatrixFourierDisintegration.mixed H G hG hβ hβ1 i a n (MatrixPredictableHaarRotation.basis k) k)
      (filtration H) Q) : Supports H Q G hH := by
  have hS2 (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ) (t : ℝ≥0) :
      MemLp (MatrixFourierDisintegration.square H G hG hβ hβ1 i a n t) 2 Q := by
    let A := MatrixFourierSquareTests.compensator H G hG hβ hβ1 i a n t
    change MemLp (fun x => M i a n t x^2-A x) 2 Q
    simpa only [pow_two] using QuadraticMomentBounds.product_sub_memLp Q
      (hM4 i a n t) (hM4 i a n t) A.continuous.stronglyMeasurable.aestronglyMeasurable ‖A‖ A.norm_coe_le_norm
  have hX2 (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ) (k : d×HaarNode) (t : ℝ≥0) :
      MemLp (MatrixFourierDisintegration.mixed H G hG hβ hβ1 i a n (MatrixPredictableHaarRotation.basis k) k t) 2 Q := by
    let A := MatrixFourierMixedTests.compensator H G hG hβ hβ1 i a n k t
    change MemLp (fun x => M i a n t x*coordinate H k t x-A x) 2 Q
    exact QuadraticMomentBounds.product_sub_memLp Q (hM4 i a n t)
      ((CanonicalInitialBrownianKernel.subgaussian H Q hBrown k t).memLp (4 : ℝ≥0))
      A.continuous.stronglyMeasurable.aestronglyMeasurable ‖A‖ A.norm_coe_le_norm
  have he (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ) := MatrixFourierDisintegration.conditional_equation H G hG hβ hβ1 i a n Q
    (hM i a n) (fun t => (hM4 i a n t).mono_exponent (by norm_num))
    (hSquare i a n) (hS2 i a n) (hMixed i a n) (hX2 i a n)
  have hall := ae_all_iff.mpr (fun i : d => ae_all_iff.mpr (fun n : ℤ =>
    (he i Complex.reCLM n).and (he i Complex.imCLM n)))
  filter_upwards [hall,CanonicalInitialBrownianKernel.law H Q hBrown] with z hz hB
  refine ⟨hB,?_⟩
  apply MatrixFourierMildRecognition.equation_of_basis (filtration H) (CanonicalInitialKernel.kernel H Q z) H
    G hG hβ hβ1 (fun p => state H p.1 p.2) (state_predictable H) hH
    (MatrixCanonicalFourierRecognition.family H (CanonicalInitialKernel.kernel H Q z) hB) (state H 0)
  have hCoord (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ)
      (hs : MatrixCanonicalFourierRecognition.Solves H (CanonicalInitialKernel.kernel H Q z) G hG hβ hβ1 hB i a n) :
      MatrixFourierMildRecognition.CoordinateEquation (filtration H) (CanonicalInitialKernel.kernel H Q z) H
        G hG hβ hβ1 (fun p => state H p.1 p.2) (state_predictable H)
        (MatrixCanonicalFourierRecognition.family H (CanonicalInitialKernel.kernel H Q z) hB) (state H 0) i a n := by
    intro t ht
    filter_upwards [hs t ht] with x hx
    have h0 : x.1 (StoppedPathPasting.origin H)=state H 0 x := by
      simp [state,clock,StoppedPathPasting.origin]
    dsimp only [CanonicalLinearFluctuation.value] at hx
    rw [min_eq_left ht,h0] at hx
    exact sub_eq_iff_eq_add'.mp hx
  intro i n
  exact ⟨hCoord i Complex.reCLM n ((hz i n).1 hB),hCoord i Complex.imCLM n ((hz i n).2 hB)⟩

end SHEStochastic.MatrixConditionalMildSolution
