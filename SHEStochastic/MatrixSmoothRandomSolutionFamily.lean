module

public import SHEStochastic.MatrixSmoothApproximation
public import SHEStochastic.MatrixRandomMildExistence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixSmoothRandomSolutionFamily
open MeasureTheory SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar MatrixSmoothApproximation
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
variable {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

/-- All smooth positive-covariance approximations have continuous native
mild solutions on the SAME space, noise and time interval. Their stochastic
time increments obey one bound independent of the approximation index and the initial law. -/
theorem exists_family (G : MatrixNonlinearCoefficient.Coefficient (Fin n))
    {K β : ℝ} (hK : 0 ≤ K) (hβ : 0 < β)
    (hG : ∀ z w, ‖G.value z-G.value w‖ ≤ K*‖z-w‖^β)
    (hH : (H : ℝ) ≤ 1) (hH0 : 0 < H) (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (N : FiniteScalarIto.Family F μ H ((Fin n) × HaarNode)) (Z : Ω → Physical (d := Fin n))
    (hZ₀ : StronglyMeasurable[F 0] Z) (hZ : MemLp Z 2 μ) :
    ∃ (U : ℕ → ℝ≥0 × Ω → Physical (d := Fin n))
      (hU : ∀ m, StronglyMeasurable[F.predictable] (U m)),
      (∀ m ω, Continuous (fun t => U m (t,ω))) ∧
      (∀ m, MatrixRandomMildExistence.Equation (coefficient G m) hH N (U m) (hU m) Z) ∧
      ∀ m s t, s ≤ H → t ≤ H →
        (∫⁻ ω, ENNReal.ofReal
          (‖(U m (s,ω)-VectorAnalyticHeat.heat s (Z ω))-(U m (t,ω)-VectorAnalyticHeat.heat t (Z ω))‖^16) ∂μ) ≤
          ENNReal.ofReal (MatrixTimeMoments.momentConstant (Fin n) (NativeMatrixEquation.cap G)*
            ((s : ℝ)-(t : ℝ))^2) := by
  have hex (m : ℕ) := MatrixRandomMildExistence.exists_solution (coefficient G m) hH hH0 hnull N
    (lipschitzConstant_nonneg G hK β m) (lipschitz G hK hβ.le hG m) Z hZ₀ hZ
  choose U hU hc he using hex
  refine ⟨U,hU,hc,he,?_⟩
  intro m s t hs ht
  exact MatrixRandomMildExistence.stochastic_increment_moment16 (coefficient G m) hH N (U m) (hU m) Z (he m) s t hs ht

end SHEStochastic.MatrixSmoothRandomSolutionFamily
