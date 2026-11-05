module

public import SHEStochastic.MatrixUnboundedGlobalRemainder

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.MatrixUnboundedDeterministicMild
open MeasureTheory ProbabilityTheory SHE MatrixInfiniteHaar MatrixFourierCoordinates Matrix
open scoped NNReal ENNReal Matrix.Norms.L2Operator MatrixOrder
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
variable {G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ} {C β : ℝ≥0}
    {hG : HolderWith C β G} {hβ : 0<β} {hβ1 : β<1}
    (u₀ : Physical (d := Fin n))
    (S : MatrixUnboundedGlobalWeakExistence.Solution G hG hβ hβ1
      (MatrixUnboundedGlobalFourierAll.pointLaw u₀))

/-- The selected law with deterministic initial data really starts at
that vector almost surely. -/
theorem initial_ae :
    MatrixGlobalBlockPath.state 1 0 =ᵐ[S.law.toMeasure] fun _ => u₀ := by
  have h : HasLaw (MatrixGlobalBlockPath.state 1 0) (Measure.dirac u₀) S.law.toMeasure := by
    refine ⟨((MatrixBlockProcessAdapted.state_adapted 1 zero_lt_one 0).mono
      ((MatrixBlockNaturalFiltration.filtration (n := n) 1).le 0)).aemeasurable, ?_⟩
    simpa [MatrixUnboundedGlobalFourierAll.pointLaw] using S.initial
  exact h.ae_eq_of_dirac

/-- The global state has a literal L2-valued mild decomposition with
the same uniquely Fourier-characterized stochastic remainder. -/
theorem mild_decomposition (T : ℝ≥0) :
    MatrixGlobalBlockPath.state 1 T =ᵐ[S.law.toMeasure]
      fun p => VectorAnalyticHeat.heat (T : ℝ) u₀+
        MatrixUnboundedGlobalRemainder.value (n := n) T p := by
  filter_upwards [initial_ae u₀ S] with p hp
  rw [←hp]
  exact MatrixUnboundedGlobalRemainder.mild_decomposition T p

/-- One initial-state null set suffices for the Hilbert decomposition
simultaneously at every nonnegative time. -/
theorem mild_decomposition_all :
    ∀ᵐ p ∂S.law.toMeasure, ∀ T : ℝ≥0,
      MatrixGlobalBlockPath.state 1 T p =
        VectorAnalyticHeat.heat (T : ℝ) u₀+
          MatrixUnboundedGlobalRemainder.value (n := n) T p := by
  filter_upwards [initial_ae u₀ S] with p hp T
  rw [←hp]
  exact MatrixUnboundedGlobalRemainder.mild_decomposition T p

/-- One global probability space, continuous vector state and coherent
Brownian family realize the unbounded equation from deterministic L2 data.
The stochastic remainder is Hilbert-valued and uniquely specified by its
actual Fourier Ito integrals at every fixed time. -/
theorem exists_fourier_mild
    (G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β<1)
    (u₀ : Physical (d := Fin n)) (ell : ℝ) (hell : 0<ell)
    (hLower : ∀ z,ell • (1 : Matrix (Fin n) (Fin n) ℝ)≤G z*(G z)ᴴ) :
    ∃ S : MatrixUnboundedGlobalWeakExistence.Solution G hG hβ hβ1
        (MatrixUnboundedGlobalFourierAll.pointLaw u₀),
      (∀ T, MatrixGlobalBlockPath.state 1 T =ᵐ[S.law.toMeasure]
        fun p => VectorAnalyticHeat.heat (T : ℝ) u₀+
          MatrixUnboundedGlobalRemainder.value (n := n) T p) ∧
      ∀ T i a m,
        (fun p => coordinate i a m (MatrixUnboundedGlobalRemainder.value (n := n) T p))
          =ᵐ[S.law.toMeasure]
        fun p => Real.exp (-(T : ℝ)*(m : ℝ)^2)*
          MatrixUnboundedGlobalFourierStep.value S T T i a m p := by
  obtain ⟨R⟩ := MatrixUnboundedGlobalFourierAll.exists_deterministic_full_solution
    G hG hβ hβ1 u₀ ell hell hLower
  exact ⟨R.base, fun T => mild_decomposition u₀ R.base T,
    fun T i a m => MatrixUnboundedGlobalRemainder.fourier_coordinate R.base T i a m⟩

end SHEStochastic.MatrixUnboundedDeterministicMild
